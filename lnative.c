#define lnative_c
#define LUA_CORE

#include "lprefix.h"
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "lua.h"
#include "lauxlib.h"
#include "lapi.h"
#include "ldebug.h"
#include "ldo.h"
#include "lfunc.h"
#include "lgc.h"
#include "lmem.h"
#include "lnative.h"
#include "lobject.h"
#include "lopcodes.h"
#include "lstate.h"
#include "lstring.h"
#include "ltm.h"

//===------------------------------------------------------------------===//
// Validation //

static int NativeError(char *Message, size_t Size, const char *Text) {
  if (Message != NULL && Size != 0)
    (void)snprintf(Message, Size, "%s", Text);
  return 1;
}

static int NativeBinary(MLuaNativeOpcode Opcode) {
  return Opcode >= MLUA_NATIVE_ADD && Opcode <= MLUA_NATIVE_SHR;
}

static int NativeComparison(MLuaNativeOpcode Opcode) {
  return Opcode >= MLUA_NATIVE_EQ && Opcode <= MLUA_NATIVE_LE;
}

static int NativeRegisterOperands(MLuaNativeOpcode Opcode) {
  return NativeBinary(Opcode) || NativeComparison(Opcode) ||
         Opcode == MLUA_NATIVE_GET_TABLE || Opcode == MLUA_NATIVE_SET_TABLE ||
         Opcode == MLUA_NATIVE_CONCAT;
}

static unsigned NativeWidth(MLuaNativeOpcode Opcode) {
  if (NativeComparison(Opcode)) return 4u;
  if (Opcode == MLUA_NATIVE_NEW_TABLE || Opcode == MLUA_NATIVE_SET_LIST || Opcode == MLUA_NATIVE_ITER_STEP) return 2u;
  if (NativeBinary(Opcode) || Opcode == MLUA_NATIVE_BRANCH) return 2u;
  return Opcode == MLUA_NATIVE_CONCAT ? 3u : 1u;
}

typedef struct NativeFlowState {
  uint64_t Initialized[4];
  uint64_t Numeric[4], Generic[4], Tables[4], Captured[4], Closing[4];
  int Open;
  uint32_t Next;
  unsigned char Reached;
  unsigned char Queued;
} NativeFlowState;

static int NativeInitialized(const NativeFlowState *State, unsigned Register) {
  return (State->Initialized[Register / 64] & (UINT64_C(1) << (Register % 64))) != 0;
}

static void NativeSetInitialized(NativeFlowState *State, unsigned Register, int Value) {
  const uint64_t Bit = UINT64_C(1) << (Register % 64);
  if (Value) State->Initialized[Register / 64] |= Bit;
  else State->Initialized[Register / 64] &= ~Bit;
}

static int NativeBit(const uint64_t *Bits, unsigned Index) {
  return (Bits[Index / 64] & (UINT64_C(1) << (Index % 64))) != 0;
}

static void NativeBitSet(uint64_t *Bits, unsigned Index, int Value) {
  const uint64_t Bit = UINT64_C(1) << (Index % 64);
  if (Value) Bits[Index / 64] |= Bit;
  else Bits[Index / 64] &= ~Bit;
}

static int NativeTouch(NativeFlowState *State, unsigned Register, int Initialized) {
  unsigned Root = Register > 2 ? Register - 2 : 0;
  if (NativeBit(State->Closing, Register)) return 1;
  for (; Root <= Register; Root++) {
    NativeBitSet(State->Numeric, Root, 0);
    NativeBitSet(State->Generic, Root, 0);
  }
  NativeBitSet(State->Tables, Register, 0);
  NativeSetInitialized(State, Register, Initialized);
  return 0;
}

static int NativeMerge(NativeFlowState *States, uint32_t Target,
                       const NativeFlowState *Incoming, uint32_t *Head, uint32_t *Tail) {
  NativeFlowState *State = &States[Target];
  unsigned Index;
  int Changed = 0;
  if (!State->Reached) {
    *State = *Incoming;
    State->Reached = 1;
    State->Queued = 0;
    Changed = 1;
  } else {
    if (State->Open != Incoming->Open) return 1;
    for (Index = 0; Index < 4; Index++) {
      uint64_t Merged;
      if (State->Closing[Index] != Incoming->Closing[Index]) return 1;
#define NATIVE_INTERSECT(Field) \
      Merged = State->Field[Index] & Incoming->Field[Index]; \
      if (Merged != State->Field[Index]) Changed = 1; \
      State->Field[Index] = Merged
      NATIVE_INTERSECT(Initialized);
      NATIVE_INTERSECT(Numeric);
      NATIVE_INTERSECT(Generic);
      NATIVE_INTERSECT(Tables);
#undef NATIVE_INTERSECT
      Merged = State->Captured[Index] | Incoming->Captured[Index];
      if (Merged != State->Captured[Index]) Changed = 1;
      State->Captured[Index] = Merged;
    }
  }
  if (Changed && !State->Queued) {
    State->Queued = 1;
    State->Next = UINT32_MAX;
    if (*Tail != UINT32_MAX) States[*Tail].Next = Target;
    else *Head = Target;
    *Tail = Target;
  }
  return 0;
}

static size_t NativeUpvalueCount(const MLuaNativeImage *Image) {
  return Image->FormatVersion == 0 ? 1u : Image->UpvalueCount;
}

static int NativeValidateFlow(const MLuaNativeImage *Image, NativeFlowState *States,
                              size_t *Work, char *Message, size_t Size) {
  uint32_t Head = 0, Tail = 0;
  const char *Error = NULL;
  memset(States, 0, Image->CodeCount * sizeof(NativeFlowState));
  States[0].Reached = States[0].Queued = 1;
  States[0].Open = -1;
  States[0].Next = UINT32_MAX;
  { unsigned Parameter;
    for (Parameter = 0; Parameter < Image->ParameterCount + Image->Vararg; Parameter++)
      NativeSetInitialized(&States[0], Parameter, 1);
  }
  while (Head != UINT32_MAX) {
    const uint32_t PC = Head;
    const MLuaNativeInstruction *I = &Image->Code[PC];
    NativeFlowState Out = States[PC];
    const unsigned A = I->A, B = I->B, C = I->C;
    unsigned Index;
    int TouchError = 0;
    Head = States[PC].Next;
    if (Head == UINT32_MAX) Tail = UINT32_MAX;
    States[PC].Queued = 0;
    if (++(*Work) > 8388608u) { Error = "native validation work budget exceeded"; break; }
    if (Out.Open >= 0 && !((I->Opcode == MLUA_NATIVE_CALL && B == 0) ||
                           (I->Opcode == MLUA_NATIVE_RETURN && B == 0) ||
                           I->Opcode == MLUA_NATIVE_SET_LIST)) {
      Error = "unconsumed native open results"; break;
    }
#define NATIVE_TOUCH(Register, Initialized) \
    (TouchError |= NativeTouch(&Out, (Register), (Initialized)))
    if (NativeRegisterOperands(I->Opcode)) {
      if (!NativeInitialized(&Out, B) || !NativeInitialized(&Out, C) ||
          (I->Opcode == MLUA_NATIVE_SET_TABLE && !NativeInitialized(&Out, A))) {
        Error = "uninitialized native input registers"; break;
      }
      if (I->Opcode != MLUA_NATIVE_SET_TABLE) {
        NATIVE_TOUCH(A, 1);
        if (I->Opcode == MLUA_NATIVE_CONCAT)
          for (Index = A + 1; Index < Image->StackSize; Index++) NATIVE_TOUCH(Index, 0);
      }
    } else switch (I->Opcode) {
      case MLUA_NATIVE_MOVE: case MLUA_NATIVE_UNM: case MLUA_NATIVE_BNOT:
      case MLUA_NATIVE_NOT: case MLUA_NATIVE_LEN:
        if (!NativeInitialized(&Out, B)) Error = "uninitialized native operand";
        NATIVE_TOUCH(A, 1);
        break;
      case MLUA_NATIVE_LOAD_CONSTANT: case MLUA_NATIVE_LOAD_BOOLEAN:
      case MLUA_NATIVE_GET_ENVIRONMENT: case MLUA_NATIVE_GET_UPVALUE:
        NATIVE_TOUCH(A, 1);
        break;
      case MLUA_NATIVE_NEW_TABLE:
        NATIVE_TOUCH(A, 1);
        for (Index = A + 1; Index < Image->StackSize; Index++) NATIVE_TOUCH(Index, 0);
        if (!NativeBit(Out.Captured, A)) NativeBitSet(Out.Tables, A, 1);
        break;
      case MLUA_NATIVE_SET_LIST:
        if (!NativeBit(Out.Tables, A) || Out.Open < 0 || (unsigned)Out.Open <= A)
          Error = "invalid native open table list";
        else for (Index = A + 1; Index < (unsigned)Out.Open; Index++)
          if (!NativeInitialized(&Out, Index)) Error = "uninitialized native list prefix";
        Out.Open = -1;
        break;
      case MLUA_NATIVE_LOAD_NIL:
        for (Index = A; Index <= A + B; Index++) NATIVE_TOUCH(Index, 1);
        break;
      case MLUA_NATIVE_SET_ENVIRONMENT: case MLUA_NATIVE_SET_UPVALUE: case MLUA_NATIVE_BRANCH:
        if (!NativeInitialized(&Out, A)) Error = "uninitialized native environment/condition";
        break;
      case MLUA_NATIVE_CALL:
        if (B == 0 && (Out.Open < 0 || (unsigned)Out.Open < A + 1)) {
          Error = "invalid native open arguments"; break;
        }
        for (Index = A; Index < (B == 0 ? (unsigned)Out.Open : A + B); Index++)
          if (!NativeInitialized(&Out, Index)) Error = "uninitialized native call argument";
        for (Index = A; Index < Image->StackSize; Index++) NATIVE_TOUCH(Index, 0);
        Out.Open = C == 0 ? (int)A : -1;
        for (Index = A; C > 1 && Index < A + C - 1; Index++) NativeSetInitialized(&Out, Index, 1);
        break;
      case MLUA_NATIVE_RETURN:
        if (B == 0 && (Out.Open < 0 || (unsigned)Out.Open < A)) {
          Error = "invalid native open return"; break;
        }
        for (Index = A; Index < (B == 0 ? (unsigned)Out.Open : A + B - 1); Index++)
          if (!NativeInitialized(&Out, Index)) Error = "uninitialized native return value";
        break;
      case MLUA_NATIVE_CLOSURE: {
        const MLuaNativeImage *Child = &Image->Children[B];
        size_t Upvalue;
        for (Upvalue = 0; Upvalue < Child->UpvalueCount; Upvalue++) {
          unsigned Register = Child->Upvalues[Upvalue].Index;
          if (!Child->Upvalues[Upvalue].InStack) continue;
          if (!NativeInitialized(&Out, Register)) Error = "uninitialized native captured register";
          NativeBitSet(Out.Captured, Register, 1);
          { unsigned Root = Register > 2 ? Register - 2 : 0;
            for (; Root <= Register; Root++) {
              NativeBitSet(Out.Numeric, Root, 0);
              NativeBitSet(Out.Generic, Root, 0);
            }
          }
          NativeBitSet(Out.Tables, Register, 0);
        }
        NATIVE_TOUCH(A, 1);
        for (Index = A + 1; Index < Image->StackSize; Index++) NATIVE_TOUCH(Index, 0);
        break;
      }
      case MLUA_NATIVE_VARARG:
        if (B == 0)
          for (Index = A; Index < Image->StackSize; Index++) NATIVE_TOUCH(Index, 0);
        Out.Open = B == 0 ? (int)A : -1;
        for (Index = A; B > 1 && Index < A + B - 1; Index++) NATIVE_TOUCH(Index, 1);
        break;
      case MLUA_NATIVE_FOR_PREP:
      case MLUA_NATIVE_ITER_PREP:
        for (Index = A; Index < A + (I->Opcode == MLUA_NATIVE_FOR_PREP ? 3u : 4u); Index++) {
          if (!NativeInitialized(&Out, Index) || NativeBit(Out.Captured, Index))
            Error = "invalid native loop preparation registers";
          NATIVE_TOUCH(Index, 1);
        }
        if (I->Opcode == MLUA_NATIVE_FOR_PREP) NativeBitSet(Out.Numeric, A, 1);
        else {
          for (Index = A + 2; Index < Image->StackSize; Index++)
            if (NativeBit(Out.Closing, Index)) Error = "unordered native closing register";
          NativeBitSet(Out.Closing, A + 2, 1);
          NativeBitSet(Out.Generic, A, 1);
        }
        break;
      case MLUA_NATIVE_FOR_STEP:
        if (!NativeBit(Out.Numeric, A)) Error = "native numeric loop without prepared state";
        break;
      case MLUA_NATIVE_ITER_STEP:
        if (!NativeBit(Out.Generic, A)) Error = "native iterator without prepared state";
        for (Index = A + 3; Index < Image->StackSize; Index++) NATIVE_TOUCH(Index, 0);
        for (Index = A + 3; Index < A + 3 + C; Index++) NativeSetInitialized(&Out, Index, 1);
        break;
      case MLUA_NATIVE_CLOSE:
        for (Index = A; Index < Image->StackSize; Index++) {
          NativeBitSet(Out.Captured, Index, 0);
          NativeBitSet(Out.Closing, Index, 0);
          if (Index >= 2) NativeBitSet(Out.Generic, Index - 2, 0);
        }
        break;
      case MLUA_NATIVE_TBC:
        if (!NativeInitialized(&Out, A)) Error = "uninitialized native closing register";
        else {
          for (Index = A; Index < Image->StackSize; Index++)
            if (NativeBit(Out.Closing, Index)) Error = "unordered native closing register";
          NativeBitSet(Out.Closing, A, 1);
        }
        break;
      case MLUA_NATIVE_JUMP: break;
      default: Error = "unsupported native flow opcode"; break;
    }
#undef NATIVE_TOUCH
    if (TouchError) Error = "native write overlaps active closing register";
    if (Error != NULL) break;
    if (I->Opcode == MLUA_NATIVE_RETURN) continue;
    if (I->Opcode == MLUA_NATIVE_JUMP || I->Opcode == MLUA_NATIVE_BRANCH ||
        I->Opcode == MLUA_NATIVE_FOR_PREP || I->Opcode == MLUA_NATIVE_FOR_STEP ||
        I->Opcode == MLUA_NATIVE_ITER_PREP || I->Opcode == MLUA_NATIVE_ITER_STEP) {
      const uint32_t Target = I->Opcode == MLUA_NATIVE_FOR_PREP ? B + 1 : B;
      if (NativeMerge(States, Target, &Out, &Head, &Tail)) {
        Error = "inconsistent native state at merge"; break;
      }
      if (I->Opcode == MLUA_NATIVE_JUMP || I->Opcode == MLUA_NATIVE_ITER_PREP) continue;
    }
    if (PC + 1 >= Image->CodeCount) { Error = "native control flow falls outside image"; break; }
    if (NativeMerge(States, PC + 1, &Out, &Head, &Tail)) {
      Error = "inconsistent native state at merge"; break;
    }
  }
  return Error != NULL ? NativeError(Message, Size, Error) : 0;
}

static int NativeParseNumber(const char *Bytes, size_t Size, TValue *Value) {
  char Buffer[201];
  if (Bytes == NULL || Size == 0 || Size > 200 || memchr(Bytes, '\0', Size) != NULL) return 0;
  memcpy(Buffer, Bytes, Size);
  Buffer[Size] = '\0';
  return luaO_str2num(Buffer, Value) == Size + 1;
}

static int NativeValidateShape(const MLuaNativeImage *Image, char *Message, size_t Size) {
  size_t PC, Encoded = 0, LiteralBytes = 0;
  if (Message != NULL && Size != 0) Message[0] = '\0';
  if (Image == NULL || Image->Code == NULL || Image->CodeCount == 0 ||
      Image->CodeCount > 1048576u || Image->StackSize < 2 || Image->StackSize > 255 ||
      Image->ConstantCount > 65536u ||
      (Image->ConstantCount != 0 && Image->Constants == NULL) ||
      Image->Source == NULL || Image->SourceSize > 1048576u ||
      Image->FormatVersion > 1 || Image->ParameterCount > 254 || Image->Vararg > 1 ||
      Image->ParameterCount + Image->Vararg > Image->StackSize ||
      Image->UpvalueCount > 255 || Image->ChildCount > 4096 ||
      (Image->UpvalueCount != 0 && Image->Upvalues == NULL) ||
      (Image->ChildCount != 0 && Image->Children == NULL) ||
      (Image->FormatVersion == 0 && (Image->ParameterCount != 0 || Image->Vararg != 0 ||
                                    Image->UpvalueCount != 0 || Image->ChildCount != 0)))
    return NativeError(Message, Size, "invalid native image dimensions");
  for (PC = 0; PC < Image->ConstantCount; PC++) {
    const MLuaNativeConstant *Constant = &Image->Constants[PC];
    if (Constant->Size > 67108864u - LiteralBytes ||
        (Constant->Size != 0 && Constant->Bytes == NULL))
      return NativeError(Message, Size, "invalid native constant storage");
    LiteralBytes += Constant->Size;
    if (Constant->Kind == MLUA_NATIVE_NUMBER) {
      TValue ParsedNumber;
      if (!NativeParseNumber(Constant->Bytes, Constant->Size, &ParsedNumber))
        return NativeError(Message, Size, "invalid native number literal");
    } else if (Constant->Kind != MLUA_NATIVE_STRING)
      return NativeError(Message, Size, "invalid native constant kind");
  }
  for (PC = 0; PC < Image->CodeCount; PC++) {
    const MLuaNativeInstruction *I = &Image->Code[PC];
    const unsigned A = I->A, B = I->B, C = I->C;
    if (I->Opcode < MLUA_NATIVE_MOVE || I->Opcode > MLUA_NATIVE_TBC ||
        A >= Image->StackSize || I->Line == 0 || I->Line > INT_MAX)
      return NativeError(Message, Size, "invalid native instruction");
    if (!(NativeRegisterOperands(I->Opcode) || I->Opcode == MLUA_NATIVE_CALL ||
          I->Opcode == MLUA_NATIVE_BRANCH || I->Opcode == MLUA_NATIVE_ITER_STEP) && C != 0)
      return NativeError(Message, Size, "noncanonical native instruction operands");
    Encoded += NativeWidth(I->Opcode);
    if (Encoded > 1048576u)
      return NativeError(Message, Size, "native encoded instruction budget exceeded");
    if (NativeRegisterOperands(I->Opcode)) {
      if (B >= Image->StackSize || C >= Image->StackSize)
        return NativeError(Message, Size, "invalid native input register bounds");
      if (I->Opcode == MLUA_NATIVE_CONCAT &&
          (A + 1 >= Image->StackSize || B < A + 2 || C < A + 2))
        return NativeError(Message, Size, "invalid native concat window");
    } else switch (I->Opcode) {
      case MLUA_NATIVE_MOVE: case MLUA_NATIVE_UNM: case MLUA_NATIVE_BNOT:
      case MLUA_NATIVE_NOT: case MLUA_NATIVE_LEN:
        if (B >= Image->StackSize) return NativeError(Message, Size, "invalid native operand bounds");
        break;
      case MLUA_NATIVE_LOAD_CONSTANT:
        if (B >= Image->ConstantCount) return NativeError(Message, Size, "invalid native constant index");
        break;
      case MLUA_NATIVE_LOAD_NIL:
        if (B >= Image->StackSize - A) return NativeError(Message, Size, "invalid native nil window");
        break;
      case MLUA_NATIVE_LOAD_BOOLEAN:
        if (B > 1) return NativeError(Message, Size, "invalid native boolean");
        break;
      case MLUA_NATIVE_GET_ENVIRONMENT: case MLUA_NATIVE_SET_ENVIRONMENT:
        if (NativeUpvalueCount(Image) == 0) return NativeError(Message, Size, "missing native environment upvalue");
        if (B != 0) return NativeError(Message, Size, "noncanonical native environment operands");
        break;
      case MLUA_NATIVE_GET_UPVALUE: case MLUA_NATIVE_SET_UPVALUE:
        if (B >= NativeUpvalueCount(Image)) return NativeError(Message, Size, "invalid native upvalue index");
        break;
      case MLUA_NATIVE_CLOSURE:
        if (B >= Image->ChildCount) return NativeError(Message, Size, "invalid native child prototype index");
        break;
      case MLUA_NATIVE_NEW_TABLE:
        if (B > 1048576u) return NativeError(Message, Size, "native table allocation budget exceeded");
        break;
      case MLUA_NATIVE_SET_LIST:
        if (B > 1048576u) return NativeError(Message, Size, "native table offset budget exceeded");
        break;
      case MLUA_NATIVE_FOR_PREP:
        if (A + 2 >= Image->StackSize || B <= PC || B >= Image->CodeCount - 1 ||
            Image->Code[B].Opcode != MLUA_NATIVE_FOR_STEP || Image->Code[B].A != A ||
            Image->Code[B].B != PC + 1)
          return NativeError(Message, Size, "invalid native numeric loop layout");
        break;
      case MLUA_NATIVE_FOR_STEP:
        if (A + 2 >= Image->StackSize || B >= PC)
          return NativeError(Message, Size, "invalid native numeric loop backedge");
        break;
      case MLUA_NATIVE_ITER_PREP:
        if (A + 5 >= Image->StackSize || B <= PC || B >= Image->CodeCount - 1 ||
            Image->Code[B].Opcode != MLUA_NATIVE_ITER_STEP || Image->Code[B].A != A ||
            Image->Code[B].B != PC + 1)
          return NativeError(Message, Size, "invalid native iterator layout");
        break;
      case MLUA_NATIVE_ITER_STEP:
        if (A + 5 >= Image->StackSize || C == 0 || C > 252 ||
            A + 3 + C > Image->StackSize || B >= PC)
          return NativeError(Message, Size, "invalid native iterator window");
        break;
      case MLUA_NATIVE_CLOSE:
      case MLUA_NATIVE_TBC:
        if (B != 0) return NativeError(Message, Size, "noncanonical native close operands");
        break;
      case MLUA_NATIVE_VARARG:
        if (!Image->Vararg || B > 255 || (B > 1 && B - 1 > Image->StackSize - A))
          return NativeError(Message, Size, "invalid native vararg window");
        break;
      case MLUA_NATIVE_CALL:
        if (B > 255 || C > 255 || (B != 0 && B > Image->StackSize - A) ||
            (C > 1 && C - 1 > Image->StackSize - A))
          return NativeError(Message, Size, "invalid native call window");
        break;
      case MLUA_NATIVE_RETURN:
        if (B > 255 || (B > 1 && B - 1 > Image->StackSize - A))
          return NativeError(Message, Size, "invalid native return window");
        break;
      case MLUA_NATIVE_JUMP: case MLUA_NATIVE_BRANCH:
        if (B >= Image->CodeCount || (I->Opcode == MLUA_NATIVE_JUMP && A != 0) ||
            (I->Opcode == MLUA_NATIVE_BRANCH && C > 1))
          return NativeError(Message, Size, "invalid native branch target/operands");
        break;
      default: return NativeError(Message, Size, "unsupported native opcode");
    }
  }
  if (Image->Code[Image->CodeCount - 1].Opcode != MLUA_NATIVE_RETURN)
    return NativeError(Message, Size, "native image has no terminal return");
  return 0;
}

typedef struct NativeGraphBudget {
  const MLuaNativeImage *Ancestors[65];
  size_t Prototypes;
  size_t Instructions;
  size_t Constants;
  size_t LiteralBytes;
} NativeGraphBudget;

static int NativeValidateGraph(const MLuaNativeImage *Image, const MLuaNativeImage *Parent,
                               NativeGraphBudget *Budget, unsigned Depth,
                               char *Message, size_t Size) {
  size_t Index;
  unsigned Ancestor;
  if (Depth > 64 || ++Budget->Prototypes > 4096)
    return NativeError(Message, Size, "native prototype graph budget exceeded");
  for (Ancestor = 0; Ancestor < Depth; Ancestor++)
    if (Budget->Ancestors[Ancestor] == Image)
      return NativeError(Message, Size, "cyclic native prototype graph");
  Budget->Ancestors[Depth] = Image;
  if (NativeValidateShape(Image, Message, Size)) return 1;
  if (Parent == NULL) {
    if (Image->FormatVersion == 1 &&
        (Image->UpvalueCount != 1 || Image->Upvalues[0].InStack != 0 || Image->Upvalues[0].Index != 0))
      return NativeError(Message, Size, "native root must have one environment upvalue");
  } else if (Image->FormatVersion != 1)
    return NativeError(Message, Size, "legacy native child image is not supported");
  Budget->Instructions += Image->Vararg;
  Budget->Constants += Image->ConstantCount;
  Budget->LiteralBytes += Image->SourceSize;
  for (Index = 0; Index < Image->CodeCount; Index++) Budget->Instructions += NativeWidth(Image->Code[Index].Opcode);
  for (Index = 0; Index < Image->ConstantCount; Index++) Budget->LiteralBytes += Image->Constants[Index].Size;
  for (Index = 0; Index < Image->UpvalueCount; Index++) {
    const MLuaNativeUpvalue *Upvalue = &Image->Upvalues[Index];
    if (Upvalue->Name == NULL || Upvalue->NameSize > 1048576 || Upvalue->InStack > 1 ||
        (Parent != NULL && Upvalue->Index >= (Upvalue->InStack ? Parent->StackSize : NativeUpvalueCount(Parent))))
      return NativeError(Message, Size, "invalid native capture descriptor");
    Budget->LiteralBytes += Upvalue->NameSize;
  }
  if (Budget->Instructions > 1048576 || Budget->Constants > 65536 || Budget->LiteralBytes > 67108864)
    return NativeError(Message, Size, "native aggregate graph budget exceeded");
  for (Index = 0; Index < Image->ChildCount; Index++)
    if (NativeValidateGraph(&Image->Children[Index], Image, Budget, Depth + 1, Message, Size)) return 1;
  return 0;
}

static int NativeValidateStandalone(const MLuaNativeImage *Image, size_t *Work, char *Message, size_t Size) {
  NativeFlowState *States;
  size_t Index;
  int Status;
  States = (NativeFlowState *)malloc(Image->CodeCount * sizeof(NativeFlowState));
  if (States == NULL) return NativeError(Message, Size, "native validation workspace allocation failed");
  Status = NativeValidateFlow(Image, States, Work, Message, Size);
  free(States);
  if (Status != 0) return Status;
  for (Index = 0; Index < Image->ChildCount; Index++)
    if (NativeValidateStandalone(&Image->Children[Index], Work, Message, Size)) return 1;
  return 0;
}

int luaM_validatenative(const MLuaNativeImage *Image, char *Message, size_t Size) {
  NativeGraphBudget Budget = {{0}, 0, 0, 0, 0};
  size_t Work = 0;
  if (NativeValidateGraph(Image, NULL, &Budget, 0, Message, Size)) return 1;
  return NativeValidateStandalone(Image, &Work, Message, Size);
}

//===------------------------------------------------------------------===//
// Encoding //

static const OpCode NativeArithmeticOpcodes[] = {
  OP_ADD, OP_SUB, OP_MUL, OP_MOD, OP_POW, OP_DIV, OP_IDIV,
  OP_BAND, OP_BOR, OP_BXOR, OP_SHL, OP_SHR
};

static const TMS NativeArithmeticMetamethods[] = {
  TM_ADD, TM_SUB, TM_MUL, TM_MOD, TM_POW, TM_DIV, TM_IDIV,
  TM_BAND, TM_BOR, TM_BXOR, TM_SHL, TM_SHR
};

static const MLuaNativeConstant *NativeOperandConstant(
    const MLuaNativeImage *Image, size_t PC, unsigned Register,
    const unsigned char *Entries) {
  const MLuaNativeInstruction *Previous;
  if (PC == 0 || Entries[PC]) return NULL;
  Previous = &Image->Code[PC - 1];
  if (Previous->Opcode != MLUA_NATIVE_LOAD_CONSTANT || Previous->A != Register)
    return NULL;
  return &Image->Constants[Previous->B];
}

static Instruction NativeEncode(const MLuaNativeInstruction *I) {
  OpCode Opcode;
  if (NativeBinary(I->Opcode))
    Opcode = NativeArithmeticOpcodes[I->Opcode - MLUA_NATIVE_ADD];
  else switch (I->Opcode) {
    case MLUA_NATIVE_MOVE: Opcode = OP_MOVE; break;
    case MLUA_NATIVE_LOAD_CONSTANT: return CREATE_ABx(OP_LOADK, I->A, I->B);
    case MLUA_NATIVE_LOAD_NIL: Opcode = OP_LOADNIL; break;
    case MLUA_NATIVE_LOAD_BOOLEAN: return CREATE_ABCk(I->B ? OP_LOADTRUE : OP_LOADFALSE, I->A, 0, 0, 0);
    case MLUA_NATIVE_GET_ENVIRONMENT: return CREATE_ABCk(OP_GETUPVAL, I->A, 0, 0, 0);
    case MLUA_NATIVE_GET_UPVALUE: return CREATE_ABCk(OP_GETUPVAL, I->A, I->B, 0, 0);
    case MLUA_NATIVE_SET_ENVIRONMENT: return CREATE_ABCk(OP_SETUPVAL, I->A, 0, 0, 0);
    case MLUA_NATIVE_SET_UPVALUE: return CREATE_ABCk(OP_SETUPVAL, I->A, I->B, 0, 0);
    case MLUA_NATIVE_CLOSURE: return CREATE_ABx(OP_CLOSURE, I->A, I->B);
    case MLUA_NATIVE_CLOSE: return CREATE_ABCk(OP_CLOSE, I->A, 0, 0, 0);
    case MLUA_NATIVE_TBC: return CREATE_ABCk(OP_TBC, I->A, 0, 0, 0);
    case MLUA_NATIVE_GET_TABLE: Opcode = OP_GETTABLE; break;
    case MLUA_NATIVE_SET_TABLE: Opcode = OP_SETTABLE; break;
    case MLUA_NATIVE_UNM: Opcode = OP_UNM; break;
    case MLUA_NATIVE_BNOT: Opcode = OP_BNOT; break;
    case MLUA_NATIVE_NOT: Opcode = OP_NOT; break;
    case MLUA_NATIVE_LEN: Opcode = OP_LEN; break;
    case MLUA_NATIVE_CALL: Opcode = OP_CALL; break;
    case MLUA_NATIVE_RETURN: return CREATE_ABCk(OP_RETURN, I->A, I->B, 0, 0);
    default: lua_assert(0); Opcode = OP_RETURN0; break;
  }
  return CREATE_ABCk(Opcode, I->A, I->B, I->C, 0);
}

static void NativeAppend(Proto *P, int *PC, Instruction I, uint32_t Line) {
  P->code[*PC] = I;
  P->lineinfo[*PC] = ABSLINEINFO;
  P->abslineinfo[*PC].pc = *PC;
  P->abslineinfo[*PC].line = (int)Line;
  ++*PC;
}

//===------------------------------------------------------------------===//
// Installation //

static void NativeBuildProto(lua_State *L, const MLuaNativeImage *Image, Proto *P, size_t *Work) {
  char Message[160];
  NativeFlowState *States;
  size_t Index, Count = Image->Vararg;
  int *Offsets;
  unsigned char *Entries;
  int PC = 0;
  luaD_checkstack(L, 3);
  States = (NativeFlowState *)lua_newuserdatauv(L, Image->CodeCount * sizeof(NativeFlowState), 0);
  if (NativeValidateFlow(Image, States, Work, Message, sizeof(Message)))
    (void)luaL_error(L, "%s", Message);
  lua_pop(L, 1);
  Offsets = (int *)lua_newuserdatauv(L, (Image->CodeCount + 1) * sizeof(int) + Image->CodeCount, 0);
  Entries = (unsigned char *)(Offsets + Image->CodeCount + 1);
  memset(Entries, 0, Image->CodeCount);
  for (Index = 0; Index < Image->CodeCount; Index++) {
    const MLuaNativeInstruction *I = &Image->Code[Index];
    if (I->Opcode == MLUA_NATIVE_JUMP || I->Opcode == MLUA_NATIVE_BRANCH ||
        I->Opcode == MLUA_NATIVE_FOR_PREP || I->Opcode == MLUA_NATIVE_FOR_STEP ||
        I->Opcode == MLUA_NATIVE_ITER_PREP || I->Opcode == MLUA_NATIVE_ITER_STEP)
      Entries[I->B] = 1;
  }
  for (Index = 0; Index < Image->CodeCount; Index++) {
    Offsets[Index] = (int)Count;
    Count += NativeWidth(Image->Code[Index].Opcode);
  }
  Offsets[Image->CodeCount] = (int)Count;
  P->maxstacksize = (lu_byte)Image->StackSize;
  P->numparams = (lu_byte)Image->ParameterCount;
  P->flag = Image->Vararg ? PF_VAHID : 0;
  P->linedefined = (int)Image->Code[0].Line;
  P->lastlinedefined = (int)Image->Code[Image->CodeCount - 1].Line;
  P->source = luaS_newlstr(L, Image->Source, Image->SourceSize);
  luaC_objbarrier(L, P, P->source);
  P->code = luaM_newvectorchecked(L, Count, Instruction);
  P->sizecode = (int)Count;
  P->lineinfo = luaM_newvectorchecked(L, Count, ls_byte);
  P->sizelineinfo = (int)Count;
  P->abslineinfo = luaM_newvectorchecked(L, Count, AbsLineInfo);
  P->sizeabslineinfo = (int)Count;
  if (Image->Vararg) NativeAppend(P, &PC, CREATE_ABCk(OP_VARARGPREP, 0, 0, 0, 0), Image->Code[0].Line);
  for (Index = 0; Index < Image->CodeCount; Index++) {
    const MLuaNativeInstruction *I = &Image->Code[Index];
    const MLuaNativeConstant *Operand = NativeOperandConstant(
        Image, Index, I->Opcode == MLUA_NATIVE_SET_TABLE ? I->B : I->C, Entries);
    if ((I->Opcode == MLUA_NATIVE_GET_TABLE || I->Opcode == MLUA_NATIVE_SET_TABLE) &&
        Operand != NULL && Operand->Kind == MLUA_NATIVE_STRING &&
        Operand->Size <= LUAI_MAXSHORTLEN && Image->Code[Index - 1].B <= MAXARG_C) {
      const unsigned Key = Image->Code[Index - 1].B;
      NativeAppend(P, &PC, I->Opcode == MLUA_NATIVE_GET_TABLE ?
          CREATE_ABCk(OP_GETFIELD, I->A, I->B, Key, 0) :
          CREATE_ABCk(OP_SETFIELD, I->A, Key, I->C, 0), I->Line);
    } else if ((I->Opcode == MLUA_NATIVE_GET_TABLE || I->Opcode == MLUA_NATIVE_SET_TABLE) &&
               Operand != NULL && Operand->Kind == MLUA_NATIVE_NUMBER) {
      TValue Number;
      if (NativeParseNumber(Operand->Bytes, Operand->Size, &Number) && ttisinteger(&Number) &&
          ivalue(&Number) >= 0 && ivalue(&Number) <= MAXARG_C) {
        const unsigned Key = (unsigned)ivalue(&Number);
        NativeAppend(P, &PC, I->Opcode == MLUA_NATIVE_GET_TABLE ?
            CREATE_ABCk(OP_GETI, I->A, I->B, Key, 0) :
            CREATE_ABCk(OP_SETI, I->A, Key, I->C, 0), I->Line);
      } else {
        NativeAppend(P, &PC, NativeEncode(I), I->Line);
      }
    } else if (I->Opcode == MLUA_NATIVE_ADD && Operand != NULL && Operand->Kind == MLUA_NATIVE_NUMBER) {
      TValue Number;
      if (NativeParseNumber(Operand->Bytes, Operand->Size, &Number) && ttisinteger(&Number) &&
          ivalue(&Number) >= -OFFSET_sC && ivalue(&Number) <= MAXARG_C - OFFSET_sC) {
        const unsigned Immediate = (unsigned)(ivalue(&Number) + OFFSET_sC);
        NativeAppend(P, &PC, CREATE_ABCk(OP_ADDI, I->A, I->B, Immediate, 0), I->Line);
        NativeAppend(P, &PC, CREATE_ABCk(OP_MMBINI, I->B, Immediate, TM_ADD, 0), I->Line);
      } else {
        NativeAppend(P, &PC, NativeEncode(I), I->Line);
        NativeAppend(P, &PC, CREATE_ABCk(OP_MMBIN, I->B, I->C, TM_ADD, 0), I->Line);
      }
    } else if (I->Opcode == MLUA_NATIVE_NEW_TABLE) {
      const unsigned Extra = I->B / (MAXARG_vC + 1u);
      NativeAppend(P, &PC, CREATE_vABCk(OP_NEWTABLE, I->A, 0, I->B % (MAXARG_vC + 1u), Extra != 0), I->Line);
      NativeAppend(P, &PC, CREATE_Ax(OP_EXTRAARG, Extra), I->Line);
    } else if (I->Opcode == MLUA_NATIVE_SET_LIST) {
      NativeAppend(P, &PC, CREATE_vABCk(OP_SETLIST, I->A, 0, I->B % (MAXARG_vC + 1u), 1), I->Line);
      NativeAppend(P, &PC, CREATE_Ax(OP_EXTRAARG, I->B / (MAXARG_vC + 1u)), I->Line);
    } else if (I->Opcode == MLUA_NATIVE_FOR_PREP || I->Opcode == MLUA_NATIVE_FOR_STEP ||
               I->Opcode == MLUA_NATIVE_ITER_PREP || I->Opcode == MLUA_NATIVE_ITER_STEP) {
      const int Back = I->Opcode == MLUA_NATIVE_FOR_STEP || I->Opcode == MLUA_NATIVE_ITER_STEP;
      const int Iterator = I->Opcode == MLUA_NATIVE_ITER_PREP || I->Opcode == MLUA_NATIVE_ITER_STEP;
      int Delta;
      if (I->Opcode == MLUA_NATIVE_ITER_STEP)
        NativeAppend(P, &PC, CREATE_ABCk(OP_TFORCALL, I->A, 0, I->C, 0), I->Line);
      Delta = Back ? PC + 1 - Offsets[I->B] : Offsets[I->B] - PC - 1;
      if (Delta < 0 || Delta > MAXARG_Bx) (void)luaL_error(L, "native loop jump exceeds encoding range");
      NativeAppend(P, &PC, CREATE_ABx(Back ? (Iterator ? OP_TFORLOOP : OP_FORLOOP) :
                                    (Iterator ? OP_TFORPREP : OP_FORPREP), I->A, Delta), I->Line);
    } else if (I->Opcode == MLUA_NATIVE_RETURN) {
      NativeAppend(P, &PC, CREATE_ABCk(OP_RETURN, I->A, I->B,
                   Image->Vararg ? Image->ParameterCount + 1 : 0, 1), I->Line);
    } else if (I->Opcode == MLUA_NATIVE_VARARG) {
      NativeAppend(P, &PC, CREATE_ABCk(OP_VARARG, I->A, Image->ParameterCount, I->B, 0), I->Line);
    } else if (I->Opcode == MLUA_NATIVE_JUMP) {
      const int Delta = Offsets[I->B] - PC - 1;
      NativeAppend(P, &PC, CREATE_sJ(OP_JMP, Delta + OFFSET_sJ, 0), I->Line);
    } else if (I->Opcode == MLUA_NATIVE_BRANCH) {
      const int Delta = Offsets[I->B] - PC - 2;
      NativeAppend(P, &PC, CREATE_ABCk(OP_TEST, I->A, 0, 0, I->C), I->Line);
      NativeAppend(P, &PC, CREATE_sJ(OP_JMP, Delta + OFFSET_sJ, 0), I->Line);
    } else if (NativeComparison(I->Opcode)) {
      const OpCode Comparison = I->Opcode == MLUA_NATIVE_EQ ? OP_EQ :
                                I->Opcode == MLUA_NATIVE_LT ? OP_LT : OP_LE;
      NativeAppend(P, &PC, CREATE_ABCk(Comparison, I->B, I->C, 0, 1), I->Line);
      NativeAppend(P, &PC, CREATE_sJ(OP_JMP, 1 + OFFSET_sJ, 0), I->Line);
      NativeAppend(P, &PC, CREATE_ABCk(OP_LFALSESKIP, I->A, 0, 0, 0), I->Line);
      NativeAppend(P, &PC, CREATE_ABCk(OP_LOADTRUE, I->A, 0, 0, 0), I->Line);
    } else if (I->Opcode == MLUA_NATIVE_CONCAT) {
      NativeAppend(P, &PC, CREATE_ABCk(OP_MOVE, I->A, I->B, 0, 0), I->Line);
      NativeAppend(P, &PC, CREATE_ABCk(OP_MOVE, I->A + 1, I->C, 0, 0), I->Line);
      NativeAppend(P, &PC, CREATE_ABCk(OP_CONCAT, I->A, 2, 0, 0), I->Line);
    } else {
      NativeAppend(P, &PC, NativeEncode(I), I->Line);
      if (NativeBinary(I->Opcode))
        NativeAppend(P, &PC, CREATE_ABCk(OP_MMBIN, I->B, I->C,
                     NativeArithmeticMetamethods[I->Opcode - MLUA_NATIVE_ADD], 0), I->Line);
    }
  }
  lua_pop(L, 1);
  P->k = luaM_newvectorchecked(L, Image->ConstantCount, TValue);
  P->sizek = (int)Image->ConstantCount;
  for (Index = 0; Index < Image->ConstantCount; Index++) setnilvalue(&P->k[Index]);
  for (Index = 0; Index < Image->ConstantCount; Index++) {
    const MLuaNativeConstant *Constant = &Image->Constants[Index];
    if (Constant->Kind == MLUA_NATIVE_NUMBER) {
      (void)NativeParseNumber(Constant->Bytes, Constant->Size, &P->k[Index]);
    } else {
      TString *String = luaS_newlstr(L, Constant->Bytes != NULL ? Constant->Bytes : "", Constant->Size);
      setsvalue(L, &P->k[Index], String);
      luaC_objbarrier(L, P, String);
    }
  }
  P->upvalues = luaM_newvectorchecked(L, NativeUpvalueCount(Image), Upvaldesc);
  P->sizeupvalues = (int)NativeUpvalueCount(Image);
  for (Index = 0; Index < (size_t)P->sizeupvalues; Index++) {
    P->upvalues[Index].name = NULL;
    P->upvalues[Index].instack = Image->FormatVersion == 0 ? 1 : (lu_byte)Image->Upvalues[Index].InStack;
    P->upvalues[Index].idx = Image->FormatVersion == 0 ? 0 : (lu_byte)Image->Upvalues[Index].Index;
    P->upvalues[Index].kind = 0;
  }
  for (Index = 0; Index < (size_t)P->sizeupvalues; Index++) {
    P->upvalues[Index].name = Image->FormatVersion == 0 ? luaS_newliteral(L, "_ENV") :
      luaS_newlstr(L, Image->Upvalues[Index].Name, Image->Upvalues[Index].NameSize);
    luaC_objbarrier(L, P, P->upvalues[Index].name);
  }
  P->p = luaM_newvectorchecked(L, Image->ChildCount, Proto *);
  P->sizep = (int)Image->ChildCount;
  for (Index = 0; Index < Image->ChildCount; Index++) P->p[Index] = NULL;
  for (Index = 0; Index < Image->ChildCount; Index++) {
    P->p[Index] = luaF_newproto(L);
    luaC_objbarrier(L, P, P->p[Index]);
    NativeBuildProto(L, &Image->Children[Index], P->p[Index], Work);
  }
  luaF_InitFieldIC(L, P);
}

static int NativeInstall(lua_State *L) {
  const MLuaNativeImage *Image = (const MLuaNativeImage *)lua_touserdata(L, 1);
  NativeGraphBudget Budget = {{0}, 0, 0, 0, 0};
  size_t Work = 0;
  char Message[160];
  LClosure *NativeClosure;
  Proto *P;
  if (NativeValidateGraph(Image, NULL, &Budget, 0, Message, sizeof(Message)))
    return luaL_error(L, "%s", Message);
  luaD_checkstack(L, 3);
  NativeClosure = luaF_newLclosure(L, 1);
  setclLvalue2s(L, L->top.p, NativeClosure);
  api_incr_top(L);
  P = luaF_newproto(L);
  NativeClosure->p = P;
  luaC_objbarrier(L, NativeClosure, P);
  NativeBuildProto(L, Image, P, &Work);
  luaF_initupvals(L, NativeClosure);
  lua_pushglobaltable(L);
  setobj(L, NativeClosure->upvals[0]->v.p, s2v(L->top.p - 1));
  luaC_barrier(L, NativeClosure->upvals[0], s2v(L->top.p - 1));
  lua_pop(L, 1);
  return 1;
}

int luaM_loadnative(lua_State *L, const MLuaNativeImage *Image) {
  if (!lua_checkstack(L, 2)) return LUA_ERRMEM;
  lua_pushcfunction(L, NativeInstall);
  lua_pushlightuserdata(L, (void *)Image);
  return lua_pcall(L, 1, 1, 0);
}

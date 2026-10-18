#ifndef lnative_h
#define lnative_h

#include <stddef.h>
#include <stdint.h>
#if defined(__cplusplus)
extern "C" {
#endif

#include "lua.h"

//===------------------------------------------------------------------===//
// Types //

typedef enum MLuaNativeOpcode {
  MLUA_NATIVE_MOVE,
  MLUA_NATIVE_LOAD_CONSTANT,
  MLUA_NATIVE_LOAD_NIL,
  MLUA_NATIVE_LOAD_BOOLEAN,
  MLUA_NATIVE_GET_ENVIRONMENT,
  MLUA_NATIVE_SET_ENVIRONMENT,
  MLUA_NATIVE_GET_TABLE,
  MLUA_NATIVE_SET_TABLE,
  MLUA_NATIVE_ADD,
  MLUA_NATIVE_SUB,
  MLUA_NATIVE_MUL,
  MLUA_NATIVE_MOD,
  MLUA_NATIVE_POW,
  MLUA_NATIVE_DIV,
  MLUA_NATIVE_IDIV,
  MLUA_NATIVE_BAND,
  MLUA_NATIVE_BOR,
  MLUA_NATIVE_BXOR,
  MLUA_NATIVE_SHL,
  MLUA_NATIVE_SHR,
  MLUA_NATIVE_UNM,
  MLUA_NATIVE_BNOT,
  MLUA_NATIVE_NOT,
  MLUA_NATIVE_LEN,
  MLUA_NATIVE_CONCAT,
  MLUA_NATIVE_CALL,
  MLUA_NATIVE_RETURN,
  MLUA_NATIVE_JUMP,
  MLUA_NATIVE_BRANCH,
  MLUA_NATIVE_EQ,
  MLUA_NATIVE_LT,
  MLUA_NATIVE_LE,
  MLUA_NATIVE_GET_UPVALUE,
  MLUA_NATIVE_SET_UPVALUE,
  MLUA_NATIVE_CLOSURE,
  MLUA_NATIVE_CLOSE,
  MLUA_NATIVE_VARARG,
  MLUA_NATIVE_NEW_TABLE,
  MLUA_NATIVE_SET_LIST,
  MLUA_NATIVE_FOR_PREP,
  MLUA_NATIVE_FOR_STEP,
  MLUA_NATIVE_ITER_PREP,
  MLUA_NATIVE_ITER_STEP,
  MLUA_NATIVE_TBC
} MLuaNativeOpcode;

typedef enum MLuaNativeConstantKind {
  MLUA_NATIVE_NUMBER,
  MLUA_NATIVE_STRING
} MLuaNativeConstantKind;

typedef struct MLuaNativeInstruction {
  MLuaNativeOpcode Opcode;
  uint32_t A;
  uint32_t B;
  uint32_t C;
  uint32_t Line;
} MLuaNativeInstruction;

typedef struct MLuaNativeConstant {
  MLuaNativeConstantKind Kind;
  const char *Bytes;
  size_t Size;
} MLuaNativeConstant;

typedef struct MLuaNativeUpvalue {
  const char *Name;
  size_t NameSize;
  uint32_t Index;
  uint32_t InStack;
} MLuaNativeUpvalue;

typedef struct MLuaNativeImage {
  const MLuaNativeInstruction *Code;
  size_t CodeCount;
  const MLuaNativeConstant *Constants;
  size_t ConstantCount;
  const char *Source;
  size_t SourceSize;
  uint32_t StackSize;
  uint32_t FormatVersion;
  uint32_t ParameterCount;
  uint32_t Vararg;
  const MLuaNativeUpvalue *Upvalues;
  size_t UpvalueCount;
  const struct MLuaNativeImage *Children;
  size_t ChildCount;
} MLuaNativeImage;

//===------------------------------------------------------------------===//
// API //

LUA_API int luaM_validatenative(const MLuaNativeImage *Image,
                              char *Message, size_t MessageSize);
LUA_API int luaM_loadnative(lua_State *L, const MLuaNativeImage *Image);

#if defined(__cplusplus)
}
#endif

#endif

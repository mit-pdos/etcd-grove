/-
Trusted code for protobuf-go's `google.golang.org/protobuf/internal/impl` (v1.36.12), in namespace
`google_golang_org.protobuf.internal.impl` like the generated package
(`Code/google_golang_org/protobuf/internal/impl.toml`).

Every package variable of `impl` that has an initializer is trusted, with a model that does
nothing: the variable is not allocated (2026-10-20; until then each `X.init` was an axiom of the
translation, which the trust-boundary axiom `impl.opaqueInitsOk` said returns). `impl` is
translated names-only (but for the struct `MessageState`), so no translated code reads any of
these variables, and a translated reader could not load one: nothing gives a points-to for it
(the package's `isPkgInit` is `True`). Each Go initializer below returns without panicking and
has no effect a translated function can observe, so the no-op loses nothing a proof could use.
The other rung, translating them, would need `impl`'s codec functions, `reflect`, `protowire`,
`protoiface` and `protoregistry` translated, for variables whose only readers are untranslated.
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace google_golang_org.protobuf.internal.impl
section code
variable [FfiSyntax] [GoGlobalContext]

/-! ### The codec tables

`coder<Kind>`, `coder<Kind>NoZero`, `...Ptr`, `...Slice`, `...PackedSlice` (`pointerCoderFuncs{size:
..., marshal: ..., unmarshal: ..., merge: ...}`) and `coder<Kind>Value`, `...SliceValue`,
`...PackedSliceValue` (`valueCoderFuncs{...}`), `codec_gen.go` and `codec_field.go`: struct literals
of the package's (untranslated) codec functions; the enum coders are the `int32` ones
(`coderEnum = coderInt32`, `codec_unsafe.go`). Each initializer only builds a struct of function
values: it cannot panic. -/

/-- `coderMessageValue = valueCoderFuncs{...}` (`codec_field.go`): does nothing. -/
def coderMessageValue.init : val :=
  λ: <>, #()

/-- `coderGroupValue = valueCoderFuncs{...}` (`codec_field.go`): does nothing. -/
def coderGroupValue.init : val :=
  λ: <>, #()

/-- `coderMessageSliceValue = valueCoderFuncs{...}` (`codec_field.go`): does nothing. -/
def coderMessageSliceValue.init : val :=
  λ: <>, #()

/-- `coderGroupSliceValue = valueCoderFuncs{...}` (`codec_field.go`): does nothing. -/
def coderGroupSliceValue.init : val :=
  λ: <>, #()

/-- `coderBool = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBool.init : val :=
  λ: <>, #()

/-- `coderBoolNoZero = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBoolNoZero.init : val :=
  λ: <>, #()

/-- `coderBoolPtr = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBoolPtr.init : val :=
  λ: <>, #()

/-- `coderBoolSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBoolSlice.init : val :=
  λ: <>, #()

/-- `coderBoolPackedSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBoolPackedSlice.init : val :=
  λ: <>, #()

/-- `coderBoolValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBoolValue.init : val :=
  λ: <>, #()

/-- `coderBoolSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBoolSliceValue.init : val :=
  λ: <>, #()

/-- `coderBoolPackedSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBoolPackedSliceValue.init : val :=
  λ: <>, #()

/-- `coderEnumValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderEnumValue.init : val :=
  λ: <>, #()

/-- `coderEnumSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderEnumSliceValue.init : val :=
  λ: <>, #()

/-- `coderEnumPackedSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderEnumPackedSliceValue.init : val :=
  λ: <>, #()

/-- `coderInt32 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt32.init : val :=
  λ: <>, #()

/-- `coderInt32NoZero = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt32NoZero.init : val :=
  λ: <>, #()

/-- `coderInt32Ptr = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt32Ptr.init : val :=
  λ: <>, #()

/-- `coderInt32Slice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt32Slice.init : val :=
  λ: <>, #()

/-- `coderInt32PackedSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt32PackedSlice.init : val :=
  λ: <>, #()

/-- `coderInt32Value = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt32Value.init : val :=
  λ: <>, #()

/-- `coderInt32SliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt32SliceValue.init : val :=
  λ: <>, #()

/-- `coderInt32PackedSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt32PackedSliceValue.init : val :=
  λ: <>, #()

/-- `coderSint32 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint32.init : val :=
  λ: <>, #()

/-- `coderSint32NoZero = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint32NoZero.init : val :=
  λ: <>, #()

/-- `coderSint32Ptr = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint32Ptr.init : val :=
  λ: <>, #()

/-- `coderSint32Slice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint32Slice.init : val :=
  λ: <>, #()

/-- `coderSint32PackedSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint32PackedSlice.init : val :=
  λ: <>, #()

/-- `coderSint32Value = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint32Value.init : val :=
  λ: <>, #()

/-- `coderSint32SliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint32SliceValue.init : val :=
  λ: <>, #()

/-- `coderSint32PackedSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint32PackedSliceValue.init : val :=
  λ: <>, #()

/-- `coderUint32 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint32.init : val :=
  λ: <>, #()

/-- `coderUint32NoZero = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint32NoZero.init : val :=
  λ: <>, #()

/-- `coderUint32Ptr = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint32Ptr.init : val :=
  λ: <>, #()

/-- `coderUint32Slice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint32Slice.init : val :=
  λ: <>, #()

/-- `coderUint32PackedSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint32PackedSlice.init : val :=
  λ: <>, #()

/-- `coderUint32Value = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint32Value.init : val :=
  λ: <>, #()

/-- `coderUint32SliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint32SliceValue.init : val :=
  λ: <>, #()

/-- `coderUint32PackedSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint32PackedSliceValue.init : val :=
  λ: <>, #()

/-- `coderInt64 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt64.init : val :=
  λ: <>, #()

/-- `coderInt64NoZero = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt64NoZero.init : val :=
  λ: <>, #()

/-- `coderInt64Ptr = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt64Ptr.init : val :=
  λ: <>, #()

/-- `coderInt64Slice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt64Slice.init : val :=
  λ: <>, #()

/-- `coderInt64PackedSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt64PackedSlice.init : val :=
  λ: <>, #()

/-- `coderInt64Value = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt64Value.init : val :=
  λ: <>, #()

/-- `coderInt64SliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt64SliceValue.init : val :=
  λ: <>, #()

/-- `coderInt64PackedSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderInt64PackedSliceValue.init : val :=
  λ: <>, #()

/-- `coderSint64 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint64.init : val :=
  λ: <>, #()

/-- `coderSint64NoZero = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint64NoZero.init : val :=
  λ: <>, #()

/-- `coderSint64Ptr = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint64Ptr.init : val :=
  λ: <>, #()

/-- `coderSint64Slice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint64Slice.init : val :=
  λ: <>, #()

/-- `coderSint64PackedSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint64PackedSlice.init : val :=
  λ: <>, #()

/-- `coderSint64Value = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint64Value.init : val :=
  λ: <>, #()

/-- `coderSint64SliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint64SliceValue.init : val :=
  λ: <>, #()

/-- `coderSint64PackedSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSint64PackedSliceValue.init : val :=
  λ: <>, #()

/-- `coderUint64 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint64.init : val :=
  λ: <>, #()

/-- `coderUint64NoZero = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint64NoZero.init : val :=
  λ: <>, #()

/-- `coderUint64Ptr = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint64Ptr.init : val :=
  λ: <>, #()

/-- `coderUint64Slice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint64Slice.init : val :=
  λ: <>, #()

/-- `coderUint64PackedSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint64PackedSlice.init : val :=
  λ: <>, #()

/-- `coderUint64Value = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint64Value.init : val :=
  λ: <>, #()

/-- `coderUint64SliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint64SliceValue.init : val :=
  λ: <>, #()

/-- `coderUint64PackedSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderUint64PackedSliceValue.init : val :=
  λ: <>, #()

/-- `coderSfixed32 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed32.init : val :=
  λ: <>, #()

/-- `coderSfixed32NoZero = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed32NoZero.init : val :=
  λ: <>, #()

/-- `coderSfixed32Ptr = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed32Ptr.init : val :=
  λ: <>, #()

/-- `coderSfixed32Slice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed32Slice.init : val :=
  λ: <>, #()

/-- `coderSfixed32PackedSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed32PackedSlice.init : val :=
  λ: <>, #()

/-- `coderSfixed32Value = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed32Value.init : val :=
  λ: <>, #()

/-- `coderSfixed32SliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed32SliceValue.init : val :=
  λ: <>, #()

/-- `coderSfixed32PackedSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed32PackedSliceValue.init : val :=
  λ: <>, #()

/-- `coderFixed32 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed32.init : val :=
  λ: <>, #()

/-- `coderFixed32NoZero = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed32NoZero.init : val :=
  λ: <>, #()

/-- `coderFixed32Ptr = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed32Ptr.init : val :=
  λ: <>, #()

/-- `coderFixed32Slice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed32Slice.init : val :=
  λ: <>, #()

/-- `coderFixed32PackedSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed32PackedSlice.init : val :=
  λ: <>, #()

/-- `coderFixed32Value = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed32Value.init : val :=
  λ: <>, #()

/-- `coderFixed32SliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed32SliceValue.init : val :=
  λ: <>, #()

/-- `coderFixed32PackedSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed32PackedSliceValue.init : val :=
  λ: <>, #()

/-- `coderFloat = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFloat.init : val :=
  λ: <>, #()

/-- `coderFloatNoZero = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFloatNoZero.init : val :=
  λ: <>, #()

/-- `coderFloatPtr = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFloatPtr.init : val :=
  λ: <>, #()

/-- `coderFloatSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFloatSlice.init : val :=
  λ: <>, #()

/-- `coderFloatPackedSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFloatPackedSlice.init : val :=
  λ: <>, #()

/-- `coderFloatValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFloatValue.init : val :=
  λ: <>, #()

/-- `coderFloatSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFloatSliceValue.init : val :=
  λ: <>, #()

/-- `coderFloatPackedSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFloatPackedSliceValue.init : val :=
  λ: <>, #()

/-- `coderSfixed64 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed64.init : val :=
  λ: <>, #()

/-- `coderSfixed64NoZero = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed64NoZero.init : val :=
  λ: <>, #()

/-- `coderSfixed64Ptr = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed64Ptr.init : val :=
  λ: <>, #()

/-- `coderSfixed64Slice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed64Slice.init : val :=
  λ: <>, #()

/-- `coderSfixed64PackedSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed64PackedSlice.init : val :=
  λ: <>, #()

/-- `coderSfixed64Value = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed64Value.init : val :=
  λ: <>, #()

/-- `coderSfixed64SliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed64SliceValue.init : val :=
  λ: <>, #()

/-- `coderSfixed64PackedSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderSfixed64PackedSliceValue.init : val :=
  λ: <>, #()

/-- `coderFixed64 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed64.init : val :=
  λ: <>, #()

/-- `coderFixed64NoZero = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed64NoZero.init : val :=
  λ: <>, #()

/-- `coderFixed64Ptr = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed64Ptr.init : val :=
  λ: <>, #()

/-- `coderFixed64Slice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed64Slice.init : val :=
  λ: <>, #()

/-- `coderFixed64PackedSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed64PackedSlice.init : val :=
  λ: <>, #()

/-- `coderFixed64Value = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed64Value.init : val :=
  λ: <>, #()

/-- `coderFixed64SliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed64SliceValue.init : val :=
  λ: <>, #()

/-- `coderFixed64PackedSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderFixed64PackedSliceValue.init : val :=
  λ: <>, #()

/-- `coderDouble = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderDouble.init : val :=
  λ: <>, #()

/-- `coderDoubleNoZero = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderDoubleNoZero.init : val :=
  λ: <>, #()

/-- `coderDoublePtr = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderDoublePtr.init : val :=
  λ: <>, #()

/-- `coderDoubleSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderDoubleSlice.init : val :=
  λ: <>, #()

/-- `coderDoublePackedSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderDoublePackedSlice.init : val :=
  λ: <>, #()

/-- `coderDoubleValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderDoubleValue.init : val :=
  λ: <>, #()

/-- `coderDoubleSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderDoubleSliceValue.init : val :=
  λ: <>, #()

/-- `coderDoublePackedSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderDoublePackedSliceValue.init : val :=
  λ: <>, #()

/-- `coderString = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderString.init : val :=
  λ: <>, #()

/-- `coderStringValidateUTF8 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderStringValidateUTF8.init : val :=
  λ: <>, #()

/-- `coderStringNoZero = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderStringNoZero.init : val :=
  λ: <>, #()

/-- `coderStringNoZeroValidateUTF8 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderStringNoZeroValidateUTF8.init : val :=
  λ: <>, #()

/-- `coderStringPtr = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderStringPtr.init : val :=
  λ: <>, #()

/-- `coderStringPtrValidateUTF8 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderStringPtrValidateUTF8.init : val :=
  λ: <>, #()

/-- `coderStringSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderStringSlice.init : val :=
  λ: <>, #()

/-- `coderStringSliceValidateUTF8 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderStringSliceValidateUTF8.init : val :=
  λ: <>, #()

/-- `coderStringValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderStringValue.init : val :=
  λ: <>, #()

/-- `coderStringValueValidateUTF8 = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderStringValueValidateUTF8.init : val :=
  λ: <>, #()

/-- `coderStringSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderStringSliceValue.init : val :=
  λ: <>, #()

/-- `coderBytes = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBytes.init : val :=
  λ: <>, #()

/-- `coderBytesValidateUTF8 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBytesValidateUTF8.init : val :=
  λ: <>, #()

/-- `coderBytesNoZero = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBytesNoZero.init : val :=
  λ: <>, #()

/-- `coderBytesNoZeroValidateUTF8 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBytesNoZeroValidateUTF8.init : val :=
  λ: <>, #()

/-- `coderBytesSlice = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBytesSlice.init : val :=
  λ: <>, #()

/-- `coderBytesSliceValidateUTF8 = pointerCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBytesSliceValidateUTF8.init : val :=
  λ: <>, #()

/-- `coderBytesValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBytesValue.init : val :=
  λ: <>, #()

/-- `coderBytesSliceValue = valueCoderFuncs{...}` (`codec_gen.go`): does nothing. -/
def coderBytesSliceValue.init : val :=
  λ: <>, #()

/-- `coderEnumNoZero = coderInt32NoZero` (`codec_unsafe.go`): does nothing. -/
def coderEnumNoZero.init : val :=
  λ: <>, #()

/-- `coderEnum = coderInt32` (`codec_unsafe.go`): does nothing. -/
def coderEnum.init : val :=
  λ: <>, #()

/-- `coderEnumPtr = coderInt32Ptr` (`codec_unsafe.go`): does nothing. -/
def coderEnumPtr.init : val :=
  λ: <>, #()

/-- `coderEnumSlice = coderInt32Slice` (`codec_unsafe.go`): does nothing. -/
def coderEnumSlice.init : val :=
  λ: <>, #()

/-- `coderEnumPackedSlice = coderInt32PackedSlice` (`codec_unsafe.go`): does nothing. -/
def coderEnumPackedSlice.init : val :=
  λ: <>, #()

/-! ### Reflection values

`boolType = reflect.TypeOf(bool(false))`, ... (`convert.go`), `sizecacheType`,
`unknownFieldsAType`, `unknownFieldsBType`, `extensionFieldsType` (`message.go`): runtime type
descriptors, and `nilBytes = reflect.ValueOf([]byte(nil))`, `emptyBytes =
reflect.ValueOf([]byte{})` (`message_reflect_field.go`): `reflect.Value`s. The semantics has no
type descriptors (`reflect` reads them out of an interface's memory), so these are irreducible, as
Perennial's `errors.errorType`; each initializer cannot panic. -/

/-- `boolType = reflect.TypeOf(bool(false))` (`convert.go`): does nothing. -/
def boolType.init : val :=
  λ: <>, #()

/-- `int32Type = reflect.TypeOf(int32(0))` (`convert.go`): does nothing. -/
def int32Type.init : val :=
  λ: <>, #()

/-- `int64Type = reflect.TypeOf(int64(0))` (`convert.go`): does nothing. -/
def int64Type.init : val :=
  λ: <>, #()

/-- `uint32Type = reflect.TypeOf(uint32(0))` (`convert.go`): does nothing. -/
def uint32Type.init : val :=
  λ: <>, #()

/-- `uint64Type = reflect.TypeOf(uint64(0))` (`convert.go`): does nothing. -/
def uint64Type.init : val :=
  λ: <>, #()

/-- `float32Type = reflect.TypeOf(float32(0))` (`convert.go`): does nothing. -/
def float32Type.init : val :=
  λ: <>, #()

/-- `float64Type = reflect.TypeOf(float64(0))` (`convert.go`): does nothing. -/
def float64Type.init : val :=
  λ: <>, #()

/-- `stringType = reflect.TypeOf(string(""))` (`convert.go`): does nothing. -/
def stringType.init : val :=
  λ: <>, #()

/-- `bytesType = reflect.TypeOf([]byte(nil))` (`convert.go`): does nothing. -/
def bytesType.init : val :=
  λ: <>, #()

/-- `byteType = reflect.TypeOf(byte(0))` (`convert.go`): does nothing. -/
def byteType.init : val :=
  λ: <>, #()

/-- `sizecacheType = reflect.TypeOf(SizeCache(0))` (`message.go`): does nothing. -/
def sizecacheType.init : val :=
  λ: <>, #()

/-- `unknownFieldsAType = reflect.TypeOf(unknownFieldsA(nil))` (`message.go`): does nothing. -/
def unknownFieldsAType.init : val :=
  λ: <>, #()

/-- `unknownFieldsBType = reflect.TypeOf(unknownFieldsB(nil))` (`message.go`): does nothing. -/
def unknownFieldsBType.init : val :=
  λ: <>, #()

/-- `extensionFieldsType = reflect.TypeOf(ExtensionFields(nil))` (`message.go`): does nothing. -/
def extensionFieldsType.init : val :=
  λ: <>, #()

/-- `nilBytes = reflect.ValueOf([]byte(nil))` (`message_reflect_field.go`): does nothing. -/
def nilBytes.init : val :=
  λ: <>, #()

/-- `emptyBytes = reflect.ValueOf([]byte{})` (`message_reflect_field.go`): does nothing. -/
def emptyBytes.init : val :=
  λ: <>, #()

/-! ### Zero values

`boolZero = protoreflect.ValueOfBool(false)`, ..., `bytesZero = protoreflect.ValueOfBytes(nil)`
(`convert.go`): `protoreflect.Value`s (a union over `unsafe.Pointer`s, an axiomatized type here);
each `ValueOf*` builds the struct, and cannot panic. -/

/-- `boolZero = protoreflect.ValueOfBool(false)` (`convert.go`): does nothing. -/
def boolZero.init : val :=
  λ: <>, #()

/-- `int32Zero = protoreflect.ValueOfInt32(0)` (`convert.go`): does nothing. -/
def int32Zero.init : val :=
  λ: <>, #()

/-- `int64Zero = protoreflect.ValueOfInt64(0)` (`convert.go`): does nothing. -/
def int64Zero.init : val :=
  λ: <>, #()

/-- `uint32Zero = protoreflect.ValueOfUint32(0)` (`convert.go`): does nothing. -/
def uint32Zero.init : val :=
  λ: <>, #()

/-- `uint64Zero = protoreflect.ValueOfUint64(0)` (`convert.go`): does nothing. -/
def uint64Zero.init : val :=
  λ: <>, #()

/-- `float32Zero = protoreflect.ValueOfFloat32(0)` (`convert.go`): does nothing. -/
def float32Zero.init : val :=
  λ: <>, #()

/-- `float64Zero = protoreflect.ValueOfFloat64(0)` (`convert.go`): does nothing. -/
def float64Zero.init : val :=
  λ: <>, #()

/-- `stringZero = protoreflect.ValueOfString("")` (`convert.go`): does nothing. -/
def stringZero.init : val :=
  λ: <>, #()

/-- `bytesZero = protoreflect.ValueOfBytes(nil)` (`convert.go`): does nothing. -/
def bytesZero.init : val :=
  λ: <>, #()

/-! ### Errors

`errDecode`, `errRecursionDepth`, `errUnknown = errors.New("...")` (`decode.go`): `errors` is
protobuf's `internal/errors`, not translated; its `New` allocates the error and cannot panic. -/

/-- `errDecode = errors.New("cannot parse invalid wire-format data")` (`decode.go`): does nothing. -/
def errDecode.init : val :=
  λ: <>, #()

/-- `errRecursionDepth = errors.New("exceeded maximum recursion depth")` (`decode.go`): does nothing. -/
def errRecursionDepth.init : val :=
  λ: <>, #()

/-- `errUnknown = errors.New("unknown")` (`decode.go`): does nothing. -/
def errUnknown.init : val :=
  λ: <>, #()

/-! ### The rest

* `wireTypes = map[protoreflect.Kind]protowire.Type{...}` (`codec_gen.go`): a map literal of
  constants;
* `lazyUnmarshalOptions = unmarshalOptions{resolver: protoregistry.GlobalTypes, ...}`
  (`decode.go`): a struct literal, reading another package's variable;
* `enableLazy = func() int32 { if os.Getenv("GOPROTODEBUG") == "nolazy" { return 0 }; return 1 }()`
  (`lazy.go`): reads the environment;
* `aberrantProtoMethods = &protoiface.Methods{...}` (`legacy_message.go`): an allocated struct of
  function values;
* `invalidOffset = ^offset(0)`, `zeroOffset = offset(0)` (`pointer_unsafe.go`): constants of the
  `uintptr` type `offset`.

None can panic. -/

/-- `wireTypes = map[protoreflect.Kind]protowire.Type{...}` (`codec_gen.go`): does nothing. -/
def wireTypes.init : val :=
  λ: <>, #()

/-- `lazyUnmarshalOptions = unmarshalOptions{...}` (`decode.go`): does nothing. -/
def lazyUnmarshalOptions.init : val :=
  λ: <>, #()

/-- `enableLazy = func() int32 {...}()` (`lazy.go`): does nothing. -/
def enableLazy.init : val :=
  λ: <>, #()

/-- `aberrantProtoMethods = &protoiface.Methods{...}` (`legacy_message.go`): does nothing. -/
def aberrantProtoMethods.init : val :=
  λ: <>, #()

/-- `invalidOffset = ^offset(0)` (`pointer_unsafe.go`): does nothing. -/
def invalidOffset.init : val :=
  λ: <>, #()

/-- `zeroOffset = offset(0)` (`pointer_unsafe.go`): does nothing. -/
def zeroOffset.init : val :=
  λ: <>, #()

/-- The blank variables (`var _ I = (*T)(nil)`, `legacy_enum.go`, `message_reflect.go`):
assertions that a type implements an interface, which the compiler checks; Go's initializer
converts a `nil` pointer and discards it. The model does nothing. -/
def «_».init : val :=
  λ: <>, #()

end code
end google_golang_org.protobuf.internal.impl

end Perennial

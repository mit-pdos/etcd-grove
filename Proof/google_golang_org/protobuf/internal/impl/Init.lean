/-
Package initialization of `google_golang_org.protobuf.internal.impl`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.google_golang_org.protobuf.internal.pragma.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace google_golang_org.protobuf.internal.impl
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `google_golang_org.protobuf.internal.impl`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([wireTypes.init,
        boolType.init,
        int32Type.init,
        int64Type.init,
        uint32Type.init,
        uint64Type.init,
        float32Type.init,
        float64Type.init,
        stringType.init,
        bytesType.init,
        byteType.init,
        boolZero.init,
        int32Zero.init,
        int64Zero.init,
        uint32Zero.init,
        uint64Zero.init,
        float32Zero.init,
        float64Zero.init,
        stringZero.init,
        bytesZero.init,
        errDecode.init,
        errRecursionDepth.init,
        lazyUnmarshalOptions.init,
        errUnknown.init,
        coderMessageValue.init,
        coderGroupValue.init,
        coderMessageSliceValue.init,
        coderGroupSliceValue.init,
        coderBool.init,
        coderBoolNoZero.init,
        coderBoolPtr.init,
        coderBoolSlice.init,
        coderBoolPackedSlice.init,
        coderBoolValue.init,
        coderBoolSliceValue.init,
        coderBoolPackedSliceValue.init,
        coderEnumValue.init,
        coderEnumSliceValue.init,
        coderEnumPackedSliceValue.init,
        coderInt32.init,
        coderInt32NoZero.init,
        coderInt32Ptr.init,
        coderInt32Slice.init,
        coderInt32PackedSlice.init,
        coderInt32Value.init,
        coderInt32SliceValue.init,
        coderInt32PackedSliceValue.init,
        coderSint32.init,
        coderSint32NoZero.init,
        coderSint32Ptr.init,
        coderSint32Slice.init,
        coderSint32PackedSlice.init,
        coderSint32Value.init,
        coderSint32SliceValue.init,
        coderSint32PackedSliceValue.init,
        coderUint32.init,
        coderUint32NoZero.init,
        coderUint32Ptr.init,
        coderUint32Slice.init,
        coderUint32PackedSlice.init,
        coderUint32Value.init,
        coderUint32SliceValue.init,
        coderUint32PackedSliceValue.init,
        coderInt64.init,
        coderInt64NoZero.init,
        coderInt64Ptr.init,
        coderInt64Slice.init,
        coderInt64PackedSlice.init,
        coderInt64Value.init,
        coderInt64SliceValue.init,
        coderInt64PackedSliceValue.init,
        coderSint64.init,
        coderSint64NoZero.init,
        coderSint64Ptr.init,
        coderSint64Slice.init,
        coderSint64PackedSlice.init,
        coderSint64Value.init,
        coderSint64SliceValue.init,
        coderSint64PackedSliceValue.init,
        coderUint64.init,
        coderUint64NoZero.init,
        coderUint64Ptr.init,
        coderUint64Slice.init,
        coderUint64PackedSlice.init,
        coderUint64Value.init,
        coderUint64SliceValue.init,
        coderUint64PackedSliceValue.init,
        coderSfixed32.init,
        coderSfixed32NoZero.init,
        coderSfixed32Ptr.init,
        coderSfixed32Slice.init,
        coderSfixed32PackedSlice.init,
        coderSfixed32Value.init,
        coderSfixed32SliceValue.init,
        coderSfixed32PackedSliceValue.init,
        coderFixed32.init,
        coderFixed32NoZero.init,
        coderFixed32Ptr.init,
        coderFixed32Slice.init,
        coderFixed32PackedSlice.init,
        coderFixed32Value.init,
        coderFixed32SliceValue.init,
        coderFixed32PackedSliceValue.init,
        coderFloat.init,
        coderFloatNoZero.init,
        coderFloatPtr.init,
        coderFloatSlice.init,
        coderFloatPackedSlice.init,
        coderFloatValue.init,
        coderFloatSliceValue.init,
        coderFloatPackedSliceValue.init,
        coderSfixed64.init,
        coderSfixed64NoZero.init,
        coderSfixed64Ptr.init,
        coderSfixed64Slice.init,
        coderSfixed64PackedSlice.init,
        coderSfixed64Value.init,
        coderSfixed64SliceValue.init,
        coderSfixed64PackedSliceValue.init,
        coderFixed64.init,
        coderFixed64NoZero.init,
        coderFixed64Ptr.init,
        coderFixed64Slice.init,
        coderFixed64PackedSlice.init,
        coderFixed64Value.init,
        coderFixed64SliceValue.init,
        coderFixed64PackedSliceValue.init,
        coderDouble.init,
        coderDoubleNoZero.init,
        coderDoublePtr.init,
        coderDoubleSlice.init,
        coderDoublePackedSlice.init,
        coderDoubleValue.init,
        coderDoubleSliceValue.init,
        coderDoublePackedSliceValue.init,
        coderString.init,
        coderStringValidateUTF8.init,
        coderStringNoZero.init,
        coderStringNoZeroValidateUTF8.init,
        coderStringPtr.init,
        coderStringPtrValidateUTF8.init,
        coderStringSlice.init,
        coderStringSliceValidateUTF8.init,
        coderStringValue.init,
        coderStringValueValidateUTF8.init,
        coderStringSliceValue.init,
        coderBytes.init,
        coderBytesValidateUTF8.init,
        coderBytesNoZero.init,
        coderBytesNoZeroValidateUTF8.init,
        coderBytesSlice.init,
        coderBytesSliceValidateUTF8.init,
        coderBytesValue.init,
        coderBytesSliceValue.init,
        coderEnumNoZero.init,
        coderEnum.init,
        coderEnumPtr.init,
        coderEnumSlice.init,
        coderEnumPackedSlice.init,
        enableLazy.init,
        «_».init,
        «_».init,
        aberrantProtoMethods.init,
        sizecacheType.init,
        unknownFieldsAType.init,
        unknownFieldsBType.init,
        extensionFieldsType.init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        «_».init,
        nilBytes.init,
        emptyBytes.init,
        invalidOffset.init,
        zeroOffset.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

end google_golang_org.protobuf.internal.impl
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.google_golang_org.protobuf.internal.impl.Assumptions]

namespace google_golang_org.protobuf.internal.impl

set_option maxHeartbeats 8000000 in
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.protobuf.internal.impl get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.internal.impl }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply _root_.Perennial.google_golang_org.protobuf.internal.pragma.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk wireTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk boolType.init (by mem_tac))
  wp_apply (opaqueInitsOk int32Type.init (by mem_tac))
  wp_apply (opaqueInitsOk int64Type.init (by mem_tac))
  wp_apply (opaqueInitsOk uint32Type.init (by mem_tac))
  wp_apply (opaqueInitsOk uint64Type.init (by mem_tac))
  wp_apply (opaqueInitsOk float32Type.init (by mem_tac))
  wp_apply (opaqueInitsOk float64Type.init (by mem_tac))
  wp_apply (opaqueInitsOk stringType.init (by mem_tac))
  wp_apply (opaqueInitsOk bytesType.init (by mem_tac))
  wp_apply (opaqueInitsOk byteType.init (by mem_tac))
  wp_apply (opaqueInitsOk boolZero.init (by mem_tac))
  wp_apply (opaqueInitsOk int32Zero.init (by mem_tac))
  wp_apply (opaqueInitsOk int64Zero.init (by mem_tac))
  wp_apply (opaqueInitsOk uint32Zero.init (by mem_tac))
  wp_apply (opaqueInitsOk uint64Zero.init (by mem_tac))
  wp_apply (opaqueInitsOk float32Zero.init (by mem_tac))
  wp_apply (opaqueInitsOk float64Zero.init (by mem_tac))
  wp_apply (opaqueInitsOk stringZero.init (by mem_tac))
  wp_apply (opaqueInitsOk bytesZero.init (by mem_tac))
  wp_apply (opaqueInitsOk errDecode.init (by mem_tac))
  wp_apply (opaqueInitsOk errRecursionDepth.init (by mem_tac))
  wp_apply (opaqueInitsOk lazyUnmarshalOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk errUnknown.init (by mem_tac))
  wp_apply (opaqueInitsOk coderMessageValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderGroupValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderMessageSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderGroupSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBool.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBoolNoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBoolPtr.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBoolSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBoolPackedSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBoolValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBoolSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBoolPackedSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderEnumValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderEnumSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderEnumPackedSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt32.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt32NoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt32Ptr.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt32Slice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt32PackedSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt32Value.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt32SliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt32PackedSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint32.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint32NoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint32Ptr.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint32Slice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint32PackedSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint32Value.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint32SliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint32PackedSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint32.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint32NoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint32Ptr.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint32Slice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint32PackedSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint32Value.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint32SliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint32PackedSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt64.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt64NoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt64Ptr.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt64Slice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt64PackedSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt64Value.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt64SliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderInt64PackedSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint64.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint64NoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint64Ptr.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint64Slice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint64PackedSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint64Value.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint64SliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSint64PackedSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint64.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint64NoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint64Ptr.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint64Slice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint64PackedSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint64Value.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint64SliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderUint64PackedSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed32.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed32NoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed32Ptr.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed32Slice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed32PackedSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed32Value.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed32SliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed32PackedSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed32.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed32NoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed32Ptr.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed32Slice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed32PackedSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed32Value.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed32SliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed32PackedSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFloat.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFloatNoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFloatPtr.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFloatSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFloatPackedSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFloatValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFloatSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFloatPackedSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed64.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed64NoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed64Ptr.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed64Slice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed64PackedSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed64Value.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed64SliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderSfixed64PackedSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed64.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed64NoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed64Ptr.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed64Slice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed64PackedSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed64Value.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed64SliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderFixed64PackedSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderDouble.init (by mem_tac))
  wp_apply (opaqueInitsOk coderDoubleNoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderDoublePtr.init (by mem_tac))
  wp_apply (opaqueInitsOk coderDoubleSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderDoublePackedSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderDoubleValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderDoubleSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderDoublePackedSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderString.init (by mem_tac))
  wp_apply (opaqueInitsOk coderStringValidateUTF8.init (by mem_tac))
  wp_apply (opaqueInitsOk coderStringNoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderStringNoZeroValidateUTF8.init (by mem_tac))
  wp_apply (opaqueInitsOk coderStringPtr.init (by mem_tac))
  wp_apply (opaqueInitsOk coderStringPtrValidateUTF8.init (by mem_tac))
  wp_apply (opaqueInitsOk coderStringSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderStringSliceValidateUTF8.init (by mem_tac))
  wp_apply (opaqueInitsOk coderStringValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderStringValueValidateUTF8.init (by mem_tac))
  wp_apply (opaqueInitsOk coderStringSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBytes.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBytesValidateUTF8.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBytesNoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBytesNoZeroValidateUTF8.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBytesSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBytesSliceValidateUTF8.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBytesValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderBytesSliceValue.init (by mem_tac))
  wp_apply (opaqueInitsOk coderEnumNoZero.init (by mem_tac))
  wp_apply (opaqueInitsOk coderEnum.init (by mem_tac))
  wp_apply (opaqueInitsOk coderEnumPtr.init (by mem_tac))
  wp_apply (opaqueInitsOk coderEnumSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk coderEnumPackedSlice.init (by mem_tac))
  wp_apply (opaqueInitsOk enableLazy.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk aberrantProtoMethods.init (by mem_tac))
  wp_apply (opaqueInitsOk sizecacheType.init (by mem_tac))
  wp_apply (opaqueInitsOk unknownFieldsAType.init (by mem_tac))
  wp_apply (opaqueInitsOk unknownFieldsBType.init (by mem_tac))
  wp_apply (opaqueInitsOk extensionFieldsType.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk nilBytes.init (by mem_tac))
  wp_apply (opaqueInitsOk emptyBytes.init (by mem_tac))
  wp_apply (opaqueInitsOk invalidOffset.init (by mem_tac))
  wp_apply (opaqueInitsOk zeroOffset.init (by mem_tac))
  iframe Hown
  is_pkg_init_finish


end google_golang_org.protobuf.internal.impl

end init

end Perennial

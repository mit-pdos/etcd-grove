/-
Package initialization of `google_golang_org.protobuf.internal.impl`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the trusted
initializers of its variables (`X.init`, models in `TrustedCode/` that do nothing).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.google_golang_org.protobuf.internal.pragma.Init
public import Proof.runtime.PkgInitExt

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

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.google_golang_org.protobuf.internal.impl.Assumptions]

namespace google_golang_org.protobuf.internal.impl

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.protobuf.internal.impl get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.internal.impl }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (_root_.Perennial.google_golang_org.protobuf.internal.pragma.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_call  -- wireTypes: its trusted initializer does nothing
  wp_call  -- boolType: its trusted initializer does nothing
  wp_call  -- int32Type: its trusted initializer does nothing
  wp_call  -- int64Type: its trusted initializer does nothing
  wp_call  -- uint32Type: its trusted initializer does nothing
  wp_call  -- uint64Type: its trusted initializer does nothing
  wp_call  -- float32Type: its trusted initializer does nothing
  wp_call  -- float64Type: its trusted initializer does nothing
  wp_call  -- stringType: its trusted initializer does nothing
  wp_call  -- bytesType: its trusted initializer does nothing
  wp_call  -- byteType: its trusted initializer does nothing
  wp_call  -- boolZero: its trusted initializer does nothing
  wp_call  -- int32Zero: its trusted initializer does nothing
  wp_call  -- int64Zero: its trusted initializer does nothing
  wp_call  -- uint32Zero: its trusted initializer does nothing
  wp_call  -- uint64Zero: its trusted initializer does nothing
  wp_call  -- float32Zero: its trusted initializer does nothing
  wp_call  -- float64Zero: its trusted initializer does nothing
  wp_call  -- stringZero: its trusted initializer does nothing
  wp_call  -- bytesZero: its trusted initializer does nothing
  wp_call  -- errDecode: its trusted initializer does nothing
  wp_call  -- errRecursionDepth: its trusted initializer does nothing
  wp_call  -- lazyUnmarshalOptions: its trusted initializer does nothing
  wp_call  -- errUnknown: its trusted initializer does nothing
  wp_call  -- coderMessageValue: its trusted initializer does nothing
  wp_call  -- coderGroupValue: its trusted initializer does nothing
  wp_call  -- coderMessageSliceValue: its trusted initializer does nothing
  wp_call  -- coderGroupSliceValue: its trusted initializer does nothing
  wp_call  -- coderBool: its trusted initializer does nothing
  wp_call  -- coderBoolNoZero: its trusted initializer does nothing
  wp_call  -- coderBoolPtr: its trusted initializer does nothing
  wp_call  -- coderBoolSlice: its trusted initializer does nothing
  wp_call  -- coderBoolPackedSlice: its trusted initializer does nothing
  wp_call  -- coderBoolValue: its trusted initializer does nothing
  wp_call  -- coderBoolSliceValue: its trusted initializer does nothing
  wp_call  -- coderBoolPackedSliceValue: its trusted initializer does nothing
  wp_call  -- coderEnumValue: its trusted initializer does nothing
  wp_call  -- coderEnumSliceValue: its trusted initializer does nothing
  wp_call  -- coderEnumPackedSliceValue: its trusted initializer does nothing
  wp_call  -- coderInt32: its trusted initializer does nothing
  wp_call  -- coderInt32NoZero: its trusted initializer does nothing
  wp_call  -- coderInt32Ptr: its trusted initializer does nothing
  wp_call  -- coderInt32Slice: its trusted initializer does nothing
  wp_call  -- coderInt32PackedSlice: its trusted initializer does nothing
  wp_call  -- coderInt32Value: its trusted initializer does nothing
  wp_call  -- coderInt32SliceValue: its trusted initializer does nothing
  wp_call  -- coderInt32PackedSliceValue: its trusted initializer does nothing
  wp_call  -- coderSint32: its trusted initializer does nothing
  wp_call  -- coderSint32NoZero: its trusted initializer does nothing
  wp_call  -- coderSint32Ptr: its trusted initializer does nothing
  wp_call  -- coderSint32Slice: its trusted initializer does nothing
  wp_call  -- coderSint32PackedSlice: its trusted initializer does nothing
  wp_call  -- coderSint32Value: its trusted initializer does nothing
  wp_call  -- coderSint32SliceValue: its trusted initializer does nothing
  wp_call  -- coderSint32PackedSliceValue: its trusted initializer does nothing
  wp_call  -- coderUint32: its trusted initializer does nothing
  wp_call  -- coderUint32NoZero: its trusted initializer does nothing
  wp_call  -- coderUint32Ptr: its trusted initializer does nothing
  wp_call  -- coderUint32Slice: its trusted initializer does nothing
  wp_call  -- coderUint32PackedSlice: its trusted initializer does nothing
  wp_call  -- coderUint32Value: its trusted initializer does nothing
  wp_call  -- coderUint32SliceValue: its trusted initializer does nothing
  wp_call  -- coderUint32PackedSliceValue: its trusted initializer does nothing
  wp_call  -- coderInt64: its trusted initializer does nothing
  wp_call  -- coderInt64NoZero: its trusted initializer does nothing
  wp_call  -- coderInt64Ptr: its trusted initializer does nothing
  wp_call  -- coderInt64Slice: its trusted initializer does nothing
  wp_call  -- coderInt64PackedSlice: its trusted initializer does nothing
  wp_call  -- coderInt64Value: its trusted initializer does nothing
  wp_call  -- coderInt64SliceValue: its trusted initializer does nothing
  wp_call  -- coderInt64PackedSliceValue: its trusted initializer does nothing
  wp_call  -- coderSint64: its trusted initializer does nothing
  wp_call  -- coderSint64NoZero: its trusted initializer does nothing
  wp_call  -- coderSint64Ptr: its trusted initializer does nothing
  wp_call  -- coderSint64Slice: its trusted initializer does nothing
  wp_call  -- coderSint64PackedSlice: its trusted initializer does nothing
  wp_call  -- coderSint64Value: its trusted initializer does nothing
  wp_call  -- coderSint64SliceValue: its trusted initializer does nothing
  wp_call  -- coderSint64PackedSliceValue: its trusted initializer does nothing
  wp_call  -- coderUint64: its trusted initializer does nothing
  wp_call  -- coderUint64NoZero: its trusted initializer does nothing
  wp_call  -- coderUint64Ptr: its trusted initializer does nothing
  wp_call  -- coderUint64Slice: its trusted initializer does nothing
  wp_call  -- coderUint64PackedSlice: its trusted initializer does nothing
  wp_call  -- coderUint64Value: its trusted initializer does nothing
  wp_call  -- coderUint64SliceValue: its trusted initializer does nothing
  wp_call  -- coderUint64PackedSliceValue: its trusted initializer does nothing
  wp_call  -- coderSfixed32: its trusted initializer does nothing
  wp_call  -- coderSfixed32NoZero: its trusted initializer does nothing
  wp_call  -- coderSfixed32Ptr: its trusted initializer does nothing
  wp_call  -- coderSfixed32Slice: its trusted initializer does nothing
  wp_call  -- coderSfixed32PackedSlice: its trusted initializer does nothing
  wp_call  -- coderSfixed32Value: its trusted initializer does nothing
  wp_call  -- coderSfixed32SliceValue: its trusted initializer does nothing
  wp_call  -- coderSfixed32PackedSliceValue: its trusted initializer does nothing
  wp_call  -- coderFixed32: its trusted initializer does nothing
  wp_call  -- coderFixed32NoZero: its trusted initializer does nothing
  wp_call  -- coderFixed32Ptr: its trusted initializer does nothing
  wp_call  -- coderFixed32Slice: its trusted initializer does nothing
  wp_call  -- coderFixed32PackedSlice: its trusted initializer does nothing
  wp_call  -- coderFixed32Value: its trusted initializer does nothing
  wp_call  -- coderFixed32SliceValue: its trusted initializer does nothing
  wp_call  -- coderFixed32PackedSliceValue: its trusted initializer does nothing
  wp_call  -- coderFloat: its trusted initializer does nothing
  wp_call  -- coderFloatNoZero: its trusted initializer does nothing
  wp_call  -- coderFloatPtr: its trusted initializer does nothing
  wp_call  -- coderFloatSlice: its trusted initializer does nothing
  wp_call  -- coderFloatPackedSlice: its trusted initializer does nothing
  wp_call  -- coderFloatValue: its trusted initializer does nothing
  wp_call  -- coderFloatSliceValue: its trusted initializer does nothing
  wp_call  -- coderFloatPackedSliceValue: its trusted initializer does nothing
  wp_call  -- coderSfixed64: its trusted initializer does nothing
  wp_call  -- coderSfixed64NoZero: its trusted initializer does nothing
  wp_call  -- coderSfixed64Ptr: its trusted initializer does nothing
  wp_call  -- coderSfixed64Slice: its trusted initializer does nothing
  wp_call  -- coderSfixed64PackedSlice: its trusted initializer does nothing
  wp_call  -- coderSfixed64Value: its trusted initializer does nothing
  wp_call  -- coderSfixed64SliceValue: its trusted initializer does nothing
  wp_call  -- coderSfixed64PackedSliceValue: its trusted initializer does nothing
  wp_call  -- coderFixed64: its trusted initializer does nothing
  wp_call  -- coderFixed64NoZero: its trusted initializer does nothing
  wp_call  -- coderFixed64Ptr: its trusted initializer does nothing
  wp_call  -- coderFixed64Slice: its trusted initializer does nothing
  wp_call  -- coderFixed64PackedSlice: its trusted initializer does nothing
  wp_call  -- coderFixed64Value: its trusted initializer does nothing
  wp_call  -- coderFixed64SliceValue: its trusted initializer does nothing
  wp_call  -- coderFixed64PackedSliceValue: its trusted initializer does nothing
  wp_call  -- coderDouble: its trusted initializer does nothing
  wp_call  -- coderDoubleNoZero: its trusted initializer does nothing
  wp_call  -- coderDoublePtr: its trusted initializer does nothing
  wp_call  -- coderDoubleSlice: its trusted initializer does nothing
  wp_call  -- coderDoublePackedSlice: its trusted initializer does nothing
  wp_call  -- coderDoubleValue: its trusted initializer does nothing
  wp_call  -- coderDoubleSliceValue: its trusted initializer does nothing
  wp_call  -- coderDoublePackedSliceValue: its trusted initializer does nothing
  wp_call  -- coderString: its trusted initializer does nothing
  wp_call  -- coderStringValidateUTF8: its trusted initializer does nothing
  wp_call  -- coderStringNoZero: its trusted initializer does nothing
  wp_call  -- coderStringNoZeroValidateUTF8: its trusted initializer does nothing
  wp_call  -- coderStringPtr: its trusted initializer does nothing
  wp_call  -- coderStringPtrValidateUTF8: its trusted initializer does nothing
  wp_call  -- coderStringSlice: its trusted initializer does nothing
  wp_call  -- coderStringSliceValidateUTF8: its trusted initializer does nothing
  wp_call  -- coderStringValue: its trusted initializer does nothing
  wp_call  -- coderStringValueValidateUTF8: its trusted initializer does nothing
  wp_call  -- coderStringSliceValue: its trusted initializer does nothing
  wp_call  -- coderBytes: its trusted initializer does nothing
  wp_call  -- coderBytesValidateUTF8: its trusted initializer does nothing
  wp_call  -- coderBytesNoZero: its trusted initializer does nothing
  wp_call  -- coderBytesNoZeroValidateUTF8: its trusted initializer does nothing
  wp_call  -- coderBytesSlice: its trusted initializer does nothing
  wp_call  -- coderBytesSliceValidateUTF8: its trusted initializer does nothing
  wp_call  -- coderBytesValue: its trusted initializer does nothing
  wp_call  -- coderBytesSliceValue: its trusted initializer does nothing
  wp_call  -- coderEnumNoZero: its trusted initializer does nothing
  wp_call  -- coderEnum: its trusted initializer does nothing
  wp_call  -- coderEnumPtr: its trusted initializer does nothing
  wp_call  -- coderEnumSlice: its trusted initializer does nothing
  wp_call  -- coderEnumPackedSlice: its trusted initializer does nothing
  wp_call  -- enableLazy: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- aberrantProtoMethods: its trusted initializer does nothing
  wp_call  -- sizecacheType: its trusted initializer does nothing
  wp_call  -- unknownFieldsAType: its trusted initializer does nothing
  wp_call  -- unknownFieldsBType: its trusted initializer does nothing
  wp_call  -- extensionFieldsType: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- «_»: its trusted initializer does nothing
  wp_call  -- nilBytes: its trusted initializer does nothing
  wp_call  -- emptyBytes: its trusted initializer does nothing
  wp_call  -- invalidOffset: its trusted initializer does nothing
  wp_call  -- zeroOffset: its trusted initializer does nothing
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.protobuf.internal.impl get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.internal.impl }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end google_golang_org.protobuf.internal.impl

end init

end Perennial

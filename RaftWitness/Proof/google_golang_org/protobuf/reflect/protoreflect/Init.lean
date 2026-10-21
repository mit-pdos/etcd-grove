/-
Package initialization of `google_golang_org.protobuf.reflect.protoreflect`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports and runs the trusted
initializers of its variables (`X.init`, models in `TrustedCode/` that do nothing).
-/
-- The copy for the parallel tree `RaftWitness/` of `Proof/google_golang_org/protobuf/reflect/protoreflect/Init.lean` (`PART_INITS` in
-- `etc/gen-init.py`): the same, but its imports of the copied modules and of raft are the part's.
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import RaftWitness.Proof.runtime.PkgInitExt

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.google_golang_org.protobuf.reflect.protoreflect.Assumptions]

namespace google_golang_org.protobuf.reflect.protoreflect

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.protobuf.reflect.protoreflect get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.reflect.protoreflect }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_call  -- nilType: its trusted initializer does nothing
  wp_call  -- boolType: its trusted initializer does nothing
  wp_call  -- int32Type: its trusted initializer does nothing
  wp_call  -- int64Type: its trusted initializer does nothing
  wp_call  -- uint32Type: its trusted initializer does nothing
  wp_call  -- uint64Type: its trusted initializer does nothing
  wp_call  -- float32Type: its trusted initializer does nothing
  wp_call  -- float64Type: its trusted initializer does nothing
  wp_call  -- stringType: its trusted initializer does nothing
  wp_call  -- bytesType: its trusted initializer does nothing
  wp_call  -- enumType: its trusted initializer does nothing
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.google_golang_org.protobuf.reflect.protoreflect get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.reflect.protoreflect }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end google_golang_org.protobuf.reflect.protoreflect

end init

end Perennial

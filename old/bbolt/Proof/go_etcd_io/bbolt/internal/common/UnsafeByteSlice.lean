module
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeByteSlice

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem UnsafeByteSlice.wp_proof (hUnsafeAdd : UnsafeAdd.spec (GF := GF) (hG := hG)) :
    UnsafeByteSlice.spec (GF := GF) (hG := hG) := by
  intro base offset i j Hb Hi Hij Hj
  wp_start
  wp_auto
  wp_apply hUnsafeAdd
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi, Hij, Int.le_refl _, Hj⟩)]
  have Hidx : arrayIndexRef w8 (sint.Z i) (base +ₗ sint.Z offset) =
      base +ₗ (sint.Z offset + sint.Z i) := by
    unfold arrayIndexRef
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa [Loc.add] using Hb))]
    simp
  rw [Hidx]
  wp_auto
  iapply HΦ; itrivial

end proof

end bbolt
end EtcdGrove
end Perennial

/-
Proof of `Spec/.../mvcc/isTombstone.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.isTombstone


@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.isTombstone.wp_proof : mvcc.isTombstone.spec (GF := GF) (hG := hG) := by
  intro s bs dq
  wp_start as Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_if_destruct
  · have h18 : bs.length = 18 := by rw [Hlen.1, Hif]; decide
    obtain ⟨v, hv⟩ : ∃ v, bs[17]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have Hbnd : 0 ≤ sint.Z (W64 17) ∧ sint.Z (W64 17) < sint.Z s.len := ⟨by decide, by rw [Hif]; decide⟩
    simp only [Hbnd, and_self, ite_true]
    wp_apply wp_load_slice_index s (sint.Z (W64 17)) bs dq v (by decide) $$ [Hs] as Hs
    · iframe Hs; ipureintro; exact hv
    (try wp_auto)
    rw [show (decide (v = W8 116) : Bool) = mvcc.isTomb bs from
      (mvcc.isTomb_of_getElem bs v h18 hv).symm]
    iapply HΦ $$ Hs
  · have h18 : bs.length ≠ 18 := by
      intro h; apply Hif; rw [Hlen.1] at h
      have := Hlen.2; unfold sint.nat sint.Z at *; word
    rw [show (false : Bool) = mvcc.isTomb bs from (mvcc.isTomb_of_length_ne bs h18).symm]
    iapply HΦ $$ Hs

end proof

end EtcdGrove
end Perennial

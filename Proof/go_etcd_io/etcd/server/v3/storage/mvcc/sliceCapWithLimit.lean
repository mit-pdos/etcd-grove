/-
Proof of `Spec/.../mvcc/sliceCapWithLimit.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.sliceCapWithLimit

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

theorem mvcc.sliceCapWithLimit.wp_proof : mvcc.sliceCapWithLimit.spec (GF := GF) (hG := hG) := by
  intro V S _ _ _ limit s vs dq
  wp_start as Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  (try wp_auto)
  have hW : ∀ (x : w64), 0 ≤ sint.Z x → W64 ((sint.Z x).toNat : Int) = x := fun x hx => by
    unfold sint.Z at *; rw [Int.toNat_of_nonneg hx]; exact BitVec.ofInt_toInt
  have h0z : sint.Z (W64 0) = 0 := by decide
  have hlenZ : (vs.length : Int) = sint.Z s.len := by
    rw [Hlen.1]; unfold sint.nat; rw [Int.toNat_of_nonneg Hlen.2]
  have hlenW : W64 (vs.length : Int) = s.len := by rw [hlenZ]; exact BitVec.ofInt_toInt
  wp_if_destruct
  · -- `limit <= 0`: the length
    (try wp_auto)
    rw [show mvcc.capWithLimit limit vs.length = vs.length by
      unfold mvcc.capWithLimit; rw [if_pos (Or.inl (by rwa [h0z] at Hif))], hlenW]
    iapply HΦ $$ Hs
  · (try wp_auto)
    wp_if_destruct
    · -- `limit > len(s)`: the length
      (try wp_auto)
      rw [show mvcc.capWithLimit limit vs.length = vs.length by
        unfold mvcc.capWithLimit; rw [if_pos (Or.inr (by rw [hlenZ]; exact Hif))], hlenW]
      iapply HΦ $$ Hs
    · -- the limit
      (try wp_auto)
      have hpos : ¬ sint.Z limit ≤ 0 := by
        have := ‹¬ sint.Z limit ≤ sint.Z (W64 0)›; rwa [h0z] at this
      rw [show mvcc.capWithLimit limit vs.length = (sint.Z limit).toNat by
        unfold mvcc.capWithLimit; rw [if_neg]; rw [hlenZ]; omega, hW limit (by omega)]
      iapply HΦ $$ Hs

end proof

end EtcdGrove
end Perennial

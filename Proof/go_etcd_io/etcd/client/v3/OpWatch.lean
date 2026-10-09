/-
Proof of `Spec/OpWatch.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.OpWatch
public import Spec.go_etcd_io.etcd.client.v3.Op__applyOpts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem OpWatch.wp_proof (wp_applyOpts : Op.applyOpts.spec (GF := GF) (hG := hG)) :
    OpWatch.spec (GF := GF) (hG := hG) := by
  intro key sl gs
  wp_start as ⟨#Hopts, %Hnp⟩
  wp_auto
  wp_apply wp_string_to_bytes key as %ksl ⟨Hks, -⟩
  ipersist Hks
  wp_apply wp_applyOpts ret_ptr _ (OpFull.getInit key) sl gs $$ [$ret] as %op' ⟨Hret, #Hat⟩
  · iframe #
    unfold opFullAt opAt OpFields
    dsimp only [OpFull.getInit, OpFull.newOp, OpModel.zero]
    isplitl []
    · isplitl []
      · ipureintro; simp
      · iapply ownSlice_nil
    isplitl []
    · iexact Hks
    isplitl []
    · ipureintro; simp
    isplitl []
    · iapply ownSlice_nil
    · unfold opSortAt; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  -- the fields `OpWatch`'s `switch` reads are all unset
  ihave Hat' := Hat
  unfold opFullAt opAt OpFields
  icases Hat' with ⟨⟨%Hf, -⟩, -, %Ht, -, -⟩
  unfold opWatchPanics opWatchModel OpFull.watchPanics at Hnp
  simp only [not_or, ne_eq, Classical.not_not, Bool.not_eq_true] at Hnp
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := Hnp
  obtain ⟨hc, -, hs, hl, hmin, hmax, hcmin, hcmax, -, -, -, -, -, hser, -⟩ := Hf
  obtain ⟨-, -, -, -, hlease, -⟩ := Ht
  have hs' : op'.sort' = null := Classical.byContradiction fun hne => by
    rw [n3] at hs; exact absurd (hs.1 hne) (by simp)
  rw [← hlease] at n1; rw [← hl] at n2; rw [← hser] at n4; rw [← hc] at n5
  rw [← hmin] at n6; rw [← hmax] at n7; rw [← hcmin] at n8; rw [← hcmax] at n9
  wp_if_destruct
  · exfalso; simp [n1] at Hif
  wp_if_destruct
  · exfalso; simp [n2] at Hif
  wp_if_destruct
  · exfalso; simp [hs'] at Hif
  wp_if_destruct
  · exfalso; simp [n4] at Hif
  wp_if_destruct
  · exfalso; simp [n5] at Hif
  wp_if_destruct
  · exfalso; simp [n7] at Hif
  wp_if_destruct
  · exfalso; simp [n6] at Hif
  wp_if_destruct
  · exfalso; simp [n9] at Hif
  wp_if_destruct
  · exfalso; simp [n8] at Hif
  iapply HΦ
  unfold opWatchModel
  iexact Hat

end proof

end EtcdGrove
end Perennial

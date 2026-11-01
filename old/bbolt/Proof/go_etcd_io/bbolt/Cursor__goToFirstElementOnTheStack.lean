module
public import Spec.go_etcd_io.bbolt.Cursor__goToFirstElementOnTheStack
public import Proof.go_etcd_io.bbolt.CursorLemmas
public import Spec.go_etcd_io.bbolt.elemRef__isLeaf
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElement
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pgid

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

set_option maxHeartbeats 400000 in
theorem Cursor.goToFirstElementOnTheStack.wp_proof
    (hpageNode : Bucket.pageNode.spec (GF := GF) (hG := hG))
    (hisLeaf : elemRef.isLeaf.spec (GF := GF) (hG := hG))
    (hBPE : Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hPgid : branchPageElement.Pgid.spec (GF := GF) (hG := hG)) :
    Cursor.goToFirstElementOnTheStack.spec (GF := GF) (hG := hG) := by
  intro cl bl V q es pid r pg Hok Hpath
  wp_start as Hc
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  unfold curI
  icases Hc with ⟨%cv, %Hb, Hcl, Hs, Hcap, Hctx, Hpgs⟩
  wp_auto
  ihave IH : iprop(∃ (cv : Cursor) (es : List elemRef) (pid : w64) (r : elemRef) (pg : List w8),
      "c" ∷ c_ptr ↦ cl ∗ "%Hcp" ∷ ⌜cv.bucket' = bl ∧ curPath V V.root es pid r pg⌝ ∗
      "Hcl" ∷ cl ↦ cv ∗ "Hs" ∷ cv.stack' ↦* es ∗
      "Hcap" ∷ ownSliceCap elemRef cv.stack' (DFrac.own 1) ∗ "Hctx" ∷ bktCtx bl V q ∗
      "Hpgs" ∷ bktPages V q) $$ [c Hcl Hs Hcap Hctx Hpgs]
  · iexists cv, es, pid, r, pg; iframe; ipureintro; exact ⟨Hb, Hpath⟩
  clear Hpath Hb
  wp_for IH
  obtain ⟨Hb, pre, Hes, Hbr, Htop⟩ := Hcp
  subst Hes
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  simp only [List.length_append, List.length_singleton] at Hsl
  have Hix : (sint.Z (cv.stack'.len - W64 1)).toNat = pre.length := by word
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
  obtain ⟨Hwf, Hnode, Hpa, Hkind⟩ := Htop
  have Hc := pageAt_car V pid r.page' pg Hok Hpa
  obtain ⟨p1, pg1, Hpa1, Hlen, -, -, -⟩ := wfAt_page V pid Hok Hwf
  obtain ⟨-, Hpg1⟩ := pageAt_unique Hpa Hpa1
  subst Hpg1
  icases ownSlice_elem_acc (sint.Z (cv.stack'.len - W64 1)) r _ _ (pre ++ [r]) (by word)
    (by rw [Hix]; simp) $$ Hs with ⟨Hr, Hsback⟩
  icases bktPages_acc V q pid r.page' pg Hok Hpa $$ Hpgs with ⟨Hpg, Hpgsback⟩
  try wp_auto
  wp_apply hisLeaf _ r (DFrac.own 1) (DFrac.own q) pg Hnode Hc Hlen $$ [Hr Hpg] as ⟨Hr, Hpg⟩
  · iframe
  rcases Hkind with ⟨Hfl, Hi0, Hil⟩ | ⟨Hfl, Hli⟩
  · rw [Hfl, decide_eq_false (by unfold branchPageFlag; decide)]
    try wp_auto
    rw [Hnode, decide_eq_true rfl]
    try wp_auto
    wp_apply hBPE r.page' (W16 (sint.Z r.index'))
    obtain ⟨Hbw, Hkids⟩ := wfAt_child V pid r.page' pg Hok Hwf Hpa Hfl
    have Hcnt : pageCount pg < 65536 := by have := leAt_lt pg 10 2; unfold pageCount; omega
    have Hu : uint.Z (W16 (sint.Z r.index')) = (((sint.Z r.index').toNat : Nat) : Int) := by word
    have Hloc : r.page' +ₗ (16 + 16 * uint.Z (W16 (sint.Z r.index'))) =
        r.page' +ₗ ((elemOff (sint.Z r.index').toNat : Nat) : Int) := by
      rw [Hu]; unfold elemOff; congr 1
    rw [Hloc]
    have Hin' : elemOff (sint.Z r.index').toNat + 16 ≤ pg.length := by
      have := Hbw.2.2.1; unfold elemOff at *; omega
    icases (branchElem_in_page (hG := hG) r.page' _ pg _ Hin' Hc).1 $$ Hpg with ⟨Hpre, He, Hpost⟩
    wp_apply hPgid _ (branchElemOf pg _) _ $$ [He] as He
    · iframe
    ihave Hpg := (branchElem_in_page (hG := hG) r.page' _ pg _ Hin' Hc).2 $$ [$Hpre $He $Hpost]
    ispecialize Hpgsback $$ Hpg
    ihave Hs := Hsback $$ %r Hr
    rw [Hix, set_len_append]
    try simp only [branchElemOf]
    try wp_auto
    have Hcw := Hkids (sint.Z r.index').toNat (by omega)
    obtain ⟨pc, pgc, Hpac, Hlenc, -, -, Hkc⟩ := wfAt_page V _ Hok Hcw
    rw [Hb]
    wp_apply pageNode_view hpageNode bl V q _ pc pgc Hok Hcw Hpac $$ [Hctx Hpgsback] as ⟨Hctx, Hpgs⟩
    · iframe
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hs $Hcap $Hsl] as %s' ⟨Hs, Hcap, -⟩
    try wp_auto
    wp_for_post
    iframe
    iexists { bucket' := cv.bucket', stack' := s' }, pre ++ [r] ++ [{ page' := pc, node' := null, index' := W64 0 }],
      W64 (branchPgid pg (sint.Z r.index').toNat), { page' := pc, node' := null, index' := W64 0 }, pgc
    iframe
    ipureintro
    refine ⟨Hb, pre ++ [r], rfl,
      branchesTo_snoc V V.root pid pre r pg Hbr ⟨Hwf, Hnode, Hpa, Or.inl ⟨Hfl, Hi0, Hil⟩⟩ Hfl,
      Hcw, rfl, Hpac, ?_⟩
    have h0 : sint.Z (W64 0) = 0 := rfl
    rcases Hkc with ⟨Hl, -⟩ | ⟨Hbb, Hbw', -⟩
    · exact Or.inr ⟨Hl, by simp only [h0]; omega, Or.inl (by simp only [h0]; omega)⟩
    · exact Or.inl ⟨Hbb, by simp only [h0]; omega, by have := Hbw'.1; simp only [h0]; omega⟩
  · rw [Hfl, decide_eq_true (by unfold leafPageFlag; decide)]
    try wp_auto
    wp_for_post
    ispecialize Hsback $$ %r Hr
    ispecialize Hpgsback $$ Hpg
    rw [Hix, set_len_append]
    try wp_auto
    iapply HΦ
    isplitl []
    · ipureintro; exact ⟨pid, ⟨pre, rfl, Hbr, Hwf, Hnode, Hpa, Or.inr ⟨Hfl, Hli⟩⟩, Hfl⟩
    iexists cv
    iframe
    ipureintro; exact Hb

end proof

end bbolt
end EtcdGrove
end Perennial

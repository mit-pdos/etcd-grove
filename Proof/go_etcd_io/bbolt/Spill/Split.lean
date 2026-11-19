/-
`node.split` (U9a, `notes/bbolt-proof-plan.md`): unit-internal, stated and proved here over the same
resources as `node.splitTwo` (`Spill/SplitTwo`), which it calls until it does not split. The pieces
`xs` (location, struct, inodes) cover the node's inodes in order, every one fits a page
(`pieceFits`) and, split, holds at least two inodes (`piecesShape`); the first is the node itself,
the others fresh nodes of its bucket and kind, all under one parent (`parentAfter`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.SplitTwo
public import Proof.go_etcd_io.bbolt.Spill.SplitDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

private instance core_persistent (K : BC) : Persistent (K.core (GF := GF)) := by
  unfold BC.core; infer_instance

private instance reg_persistent (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

theorem node.split.wp_proof (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hV : internal.common.Inode.Value.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncSplit.spec (GF := GF) (hG := hG)) :
    node.split.spec (GF := GF) (hG := hG) := by
  intro K tx r m q nl nv ins f dqf dqt pv pcs ps Hbnd Hnan Hps
  wp_start as ⟨#Hcore, #Hreg, Hst, Hn, Hins, Hcap, Hfp, Htx, Hpar⟩
  wp_auto
  ihave Hnil := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
  ihave Hnilc := ownSliceCap_nil (V := Loc) (GF := GF)
  ihave IH : (∃ (done : List (Loc × node × List Inode)) (cl : Loc) (cv : node) (rest : List Inode)
      (pvX : node) (pcsX : List Loc) (sl : GoSlice),
      "nodes" ∷ nodes_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* done.map (·.1) ∗
      "Hslc" ∷ ownSliceCap Loc sl (DFrac.own 1) ∗
      "node" ∷ node_ptr ↦ cl ∗ "Hc" ∷ cl ↦ cv ∗ "Hci" ∷ cv.inodes' ↦* rest ∗
      "Hcc" ∷ ownSliceCap Inode cv.inodes' (DFrac.own 1) ∗
      "Hpar" ∷ parentOwn cv.parent' pvX pcsX ∗
      "Hd" ∷ ([∗list] x ∈ done, x.1 ↦ x.2.1 ∗ x.2.1.inodes' ↦* x.2.2) ∗
      "Hst" ∷ statsTok r m q ∗
      "Hfp" ∷ nv.bucket'.[Bucket, go!"FillPercent"] ↦{dqf} f ∗
      "Htx" ∷ nv.bucket'.[Bucket, go!"tx"] ↦{dqt} tx ∗
      "%Hph" ∷ ⌜splitPhase ps.toNat nl nv pv pcs done cl cv rest pvX pcsX ∧
        (done.map (·.2.2)).flatten ++ rest = ins⌝ : IProp GF)
      $$ [nodes Hnil Hnilc node Hn Hins Hcap Hpar Hst Hfp Htx]
  · iexists [], nl, nv, ins, pv, pcs, slice.nil
    simp only [named, List.map_nil]
    iframe
    isplitl []
    · iexact Hnil
    isplitl []
    · iexact Hnilc
    isplitl []
    · iapply (BigSepL.bigSepL_nil_intro (P := (iprop(True) : IProp GF))); ipureintro; trivial
    ipureintro
    exact ⟨Or.inl ⟨rfl, rfl, rfl, rfl, rfl⟩, by simp⟩
  wp_for IH
  try rw [show decide ((#true : val) = #true) = true from decide_eq_true rfl]
  try simp only [↓reduceIte]
  obtain ⟨hb, -⟩ := splitPhase_bucket Hph.1
  have Hrest : insBnd rest := by
    intro it hit; apply Hbnd it; rw [← Hph.2]; exact List.mem_append_right _ hit
  rw [← hb]
  try wp_auto
  wp_apply node.splitTwo.wp_proof hK hV hInc K tx r m q cl cv rest f dqf dqt pvX pcsX ps
    Hrest Hnan Hps $$ [Hst Hc Hci Hcc Hfp Htx Hpar] as %nx ⟨Hst, Hfp, Htx, Hpost⟩
  · iframe; isplitl []
    · iexact Hcore
    iexact Hreg
  rw [hb]
  try wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  wp_apply wp_slice_append $$ [$Hsl $Hslc $Hsl2] as %s' ⟨Hsl, Hslc, -⟩
  try wp_auto
  icases Hpost with (⟨%Hun, Hc, Hci, Hcc, Hpar⟩ | ⟨%k, %pl, %pv'', %pcs'', %Hsp, Hc, HL, Hx, HR, HRc, Hpl, Hpc, Hpcc⟩)
  · -- unsplit: the loop ends
    rw [Hun.1]
    wp_if_destruct
    · wp_for_post
      try wp_auto
      have hfin := splitPhase_final Hph.1 Hph.2 Hun.2
      ispecialize HΦ $$ %s' %(done ++ [(cl, cv, rest)])
      iapply HΦ
      iframe
      rw [List.map_append]
      iframe
      isplitl []
      · ipureintro; rw [List.map_append, List.flatten_append]; simpa using Hph.2
      rcases hfin with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨h2, hpn, hsh, hpa⟩
      · ileft
        iframe
        ipureintro; exact ⟨rfl, Hun.2⟩
      · iright
        iexists cv.parent', pvX, pcsX
        unfold parentOwn
        rw [if_neg hpn]
        icases Hpar with ⟨Hp, Hpc, Hpcc⟩
        ihave Hxs : ([∗list] x ∈ done ++ [(cl, cv, rest)], x.1 ↦ x.2.1 ∗ x.2.1.inodes' ↦* x.2.2 : IProp GF)
          $$ [Hd Hc Hci]
        · iapply BigSepL.bigSepL_snoc.2; iframe
        iframe
        isplitl []
        · ipureintro; exact h2
        ipureintro; exact ⟨hpn, hsh, by simpa only [List.map_append] using hpa⟩
    · exact absurd rfl Hif
  · -- split: the next piece
    obtain ⟨hk2, hk3, hfit, hnx, hpl, hsp⟩ := Hsp
    wp_if_destruct
    · exact absurd rfl hnx
    try wp_auto
    wp_for_post
    ihave Hxs : ([∗list] x ∈ done ++ [(cl, splitLeft cv pl k, rest.take k)],
        x.1 ↦ x.2.1 ∗ x.2.1.inodes' ↦* x.2.2 : IProp GF) $$ [Hd Hc HL]
    · iapply BigSepL.bigSepL_snoc.2; iframe
    iframe
    have hst := splitPhase_step Hph.1 hk2 hk3 hfit hnx hpl hsp
    iexists done ++ [(cl, splitLeft cv pl k, rest.take k)], nx, splitRight cv pl k, rest.drop k,
      pv'', pcs'', s'
    rw [List.map_append]
    iframe
    have hpr : (splitRight cv pl k).parent' = pl := rfl
    isplitl [Hpl Hpc Hpcc]
    · unfold parentOwn; rw [hpr, if_neg hpl]; simp only [named]; iframe
    ipureintro
    refine ⟨hst, ?_⟩
    rw [List.map_append, List.flatten_append, ← Hph.2]
    simp

end proof

end bbolt
end EtcdGrove
end Perennial

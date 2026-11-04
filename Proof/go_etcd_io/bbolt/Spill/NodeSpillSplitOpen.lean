/-
`node.spill`'s split (U9v, `notes/bbolt-proof-plan.md`): **the writer's state opened for
`n.split`** (`split_open`): `node.split`'s resources out of `wtxW` (the node's struct, inodes and
their capacity, its parent's, the bucket's `FillPercent` and `tx` fields), and back after the
split, the records related by `splitRel`. A top node (`split_open_top`) or a child
(`split_open_child`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplitObjs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section open_
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`n.split(4096)`'s postcondition** but the returned slice and the fields (its spec's). -/
def splitPost (n : Loc) (rN : NRec) (pv : node) (pcs : List Loc)
    (xs : List (Loc × node × List Inode)) : IProp GF :=
  iprop((⌜xs = [(n, rN.nv, rN.ins)] ∧ pieceFits (W64 4096).toNat rN.ins⌝ ∗ n ↦ rN.nv ∗
      rN.nv.inodes' ↦* rN.ins ∗ ownSliceCap Inode rN.nv.inodes' (DFrac.own 1) ∗
      parentOwn rN.nv.parent' pv pcs) ∨
    (∃ (pl : Loc) (pv' : node) (pcs' : List Loc),
      ⌜2 ≤ xs.length ∧ pl ≠ null ∧ piecesShape (W64 4096).toNat n rN.nv pl xs ∧
        parentAfter rN.nv pv pcs pl pv' pcs' (xs.map (·.1))⌝ ∗
      ([∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ x.2.1.inodes' ↦* x.2.2) ∗
      pl ↦ pv' ∗ pv'.children' ↦* pcs' ∗ ownSliceCap Loc pv'.children' (DFrac.own 1)))

/-- What `split_open` gives back: the writer's state on the records after the split. -/
def splitBack (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X1 : WX) (bl n : Loc) (rN : NRec)
    (xs : List (Loc × node × List Inode)) : IProp GF :=
  iprop(∃ (X2 : WX) (wss : List (List WEntry)) (pl : Loc) (rp' : NRec),
    wtxW K tx r m X2 ∗ ⌜splitRel X1 X2 bl n rN xs wss pl rp' ∧
      ∀ x ∈ xs, pieceFits 4096 x.2.2 ∧ (2 ≤ xs.length → 2 ≤ x.2.2.length)⌝)

omit hos in
theorem ite_true_acc {c : Bool} (P : IProp GF) (h : c = true) :
    (if c = true then P else emp) ⊣⊢ P := by
  rw [h]; exact .rfl

theorem splitX_handles (X : WX) (bl : Loc) (B : BRec) (a b : List (Loc × NRec)) :
    (splitX X bl B a b).handles = X.handles := rfl

theorem w4096 : (W64 4096).toNat = 4096 := rfl

/-- **The split's resources out of the writer's state, a top node** (`n`'s parent `null`). -/
theorem split_open_top (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X1 : WX) (bl n : Loc)
    (rN : NRec) (hn : X1.node bl n = some rN) (hlv : n ∈ X1.live) (hbl : rN.nv.bucket' = bl)
    (hcap : rN.capOwn = true) (hsp : rN.nv.spilled' = false) (hil : rN.ins.length = rN.ws.length)
    (hch : rN.nv.children' = slice.nil) (h0 : rN.nv.parent' = null) :
    wtxW (GF := GF) K tx r m X1 ⊢ ∃ (f : w64) (dqb : DFrac),
      ⌜¬ float64IsNaN f ∧ r.db = K.db⌝ ∗
      □ (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ K.core ∗ reg tx K.B r) ∗
      statsTok r m 1 ∗ n ↦ rN.nv ∗ rN.nv.inodes' ↦* rN.ins ∗
      ownSliceCap Inode rN.nv.inodes' (DFrac.own 1) ∗
      rN.nv.bucket'.[Bucket, go!"FillPercent"] ↦ f ∗ rN.nv.bucket'.[Bucket, go!"tx"] ↦{dqb} tx ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db ∗
      (∀ xs : List (Loc × node × List Inode), statsTok r m 1 -∗
        rN.nv.bucket'.[Bucket, go!"FillPercent"] ↦ f -∗
        rN.nv.bucket'.[Bucket, go!"tx"] ↦{dqb} tx -∗
        tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db -∗
        ⌜(xs.map (·.2.2)).flatten = rN.ins⌝ -∗
        splitPost n rN (zero_val node) [] xs -∗ splitBack K tx r m X1 bl n rN xs) := by
  obtain ⟨B, hb, hrn⟩ := node_bs_of hn
  iintro Hw
  icases (wtxW_frame K tx r m X1).1 $$ Hw with ⟨Hh, Hfills, Hdb, Hst, Hfr⟩
  icases splitFr_pers K tx r X1 $$ Hfr with ⟨#Hpers, %Hrdb, Hfr⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X1 $$ Hh
  have htx : B.bv.tx' = tx := Hok.2.2.1 bl B hb
  have hpn : rN.nv.parent' ≠ n := Hok.2.2.2.1 bl B n rN hb hrn
  icases wtxHeap_splitX tx X1 bl B [n] (fun _ => rN) hb (nodup_one n)
    (by intro l hl; rw [List.mem_singleton.1 hl]; exact hrn) $$ Hh
    with ⟨HL, Hbo, Htf, Hrf, Hback⟩
  icases fill_acc tx X1 bl Hok.1 (Hok.2.2.2.2.2 bl B hb) $$ [Hrf Hfills]
    with ⟨%f, %Hnan, Hfp, Hfpb⟩
  · iframe
  icases objOwn_bkt_tx_acc X1.v bl _ B $$ Hbo with ⟨%dqb, Htx, Htxb⟩
  icases BigSepL.bigSepL_singleton.1 $$ HL with HN
  rw [decide_eq_true hlv]
  icases (objOwn_live_node (GF := GF) X1.v n _ bl rN).1 $$ HN
    with ⟨Hn, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
  icases (ite_true_acc _ hcap).1 $$ Hcap with Hcap
  rw [hbl]
  iexists f, dqb
  rw [htx]
  iframe Hst Hn Hins Hcap Hfp Htx Hdb
  isplitl []
  · ipureintro; exact ⟨Hnan, Hrdb⟩
  isplitl []
  · iexact Hpers
  iintro %xs Hst Hfp Htx Hdb %Hflat Hpost
  icases Hfpb $$ Hfp with ⟨Hrf, Hfills⟩
  ihave Hbo := Htxb $$ Htx
  unfold splitPost splitBack
  icases Hpost with (⟨%Hone, Hn, Hins, Hcap, -⟩ | ⟨%pl, %pv', %pcs', %Hsp, Hps, Hpl, Hplc, Hplcap⟩)
  · -- unsplit
    obtain ⟨rfl, hfit⟩ := Hone
    ihave HN : objOwn X1.v n (DFrac.own 1) true (.node bl rN) $$ [Hn Hins Hcap Hws Hch Hchcap Hkey]
    · iapply (objOwn_live_node (GF := GF) X1.v n _ bl rN).2
      iframe
      iapply (ite_true_acc _ hcap).2
      iexact Hcap
    icases Hback $$ %([(n, rN)] : List (Loc × NRec)) %([] : List (Loc × NRec)) [] [HN] [Hbo] [Htf] [Hrf] [] with ⟨-, Hh⟩
    · ipureintro
      refine ⟨rfl, by simp, ?_⟩
      intro p hp; simp at hp; subst hp; exact hpn
    · iapply BigSepL.bigSepL_singleton.2
      simp only [decide_eq_true hlv]
      iexact HN
    · iexact Hbo
    · iexact Htf
    · iexact Hrf
    · iapply BigSepL.bigSepL_nil.2; iempintro
    obtain ⟨rp', hrel⟩ := splitRel_one hb hlv hbl hcap hsp hil hch [(n, rN)] (by simp)
      (List.mem_singleton_self _) (by intro p hp; simp at hp; subst hp; exact hrn)
      (by intro p hp; simp at hp; subst hp; exact Or.inl rfl) (fun h => absurd h0 h)
    iexists splitX X1 bl B [(n, rN)] [], [rN.ws], rN.nv.parent', rp'
    isplitl [Hh Hfills Hdb Hst Hfr]
    · iapply (wtxW_frame K tx r m _).2
      rw [splitFr_splitX, splitX_handles]
      iframe
    ipureintro
    refine ⟨hrel, ?_⟩
    intro x hx; simp at hx; subst hx
    exact ⟨by rw [← w4096]; exact hfit, fun h => by simp at h⟩
  · -- split, under a new parent
    obtain ⟨h2, hpl, hsh, hpa⟩ := Hsp
    obtain ⟨hpv, hpcs⟩ : pv' = newParent rN.nv pv'.children' ∧ pcs' = xs.map (·.1) := by
      rcases hpa with ⟨-, a, b⟩ | ⟨h, -⟩
      · exact ⟨a, b⟩
      · exact absurd h0 h
    have hfits := hsh.1
    icases ptsL_nodup (fun x : Loc × node × List Inode => (x.2.1.inodes' ↦* x.2.2 : IProp GF)) xs
      $$ Hps with ⟨%Hnd, Hps⟩
    icases ptsL_notin (fun x : Loc × node × List Inode => (x.2.1.inodes' ↦* x.2.2 : IProp GF)) xs
      pl pv' $$ [Hpl Hps] with ⟨%Hplx, Hpl, Hps⟩
    · iframe
    have hrel := splitRel_top hb hlv hbl hsp hil hch h0 hsh h2 hpl hpv Hflat Hnd Hplx
    obtain ⟨-, x0, rest, rfl, hx0n, hx0s, hrest⟩ := hsh
    dsimp only at hrel
    obtain ⟨hA, hB, hC, hD⟩ := hrel
    ihave Hws := bigSepL2_cut (fun it w => wOwn (GF := GF) X1.v true it w)
      ((x0 :: rest).map (·.2.2)) rN.ws (by rw [Hflat, hil]) $$ [Hws]
    · rw [Hflat]; iexact Hws
    rw [List.map_cons, cutWs]
    icases BigSepL2.bigSepL2_cons.1 $$ Hws with ⟨Hw0, Hwr⟩
    icases Hps with ⟨⟨Hx0, Hx0i⟩, Hrest⟩
    rw [hx0n]
    ihave HN := headObj X1.v bl n rN x0 (rN.ws.take x0.2.2.length) (by rw [hx0s])
      (by rw [hx0s]) $$ [Hx0 Hx0i Hw0 Hch Hchcap Hkey]
    · iframe
    ihave HT := tailObjs X1.v bl rN rest (rN.ws.drop x0.2.2.length)
      (fun x hx => by rw [(hrest x hx).2]; exact ⟨rfl, rfl⟩) $$ [Hrest Hwr]
    · iframe
    rw [hpcs]
    ihave HP := newParObj X1.v bl pl pv' ((x0 :: rest).map (·.1)) (by rw [hpv]; rfl)
      (by rw [hpv]; rfl) $$ [Hpl Hplc Hplcap]
    · iframe
    have e1 : (pieceRecs rN false (x0 :: rest) (cutWs ((x0 :: rest).map (·.2.2)) rN.ws) true).take 1
        = [(n, splitRec rN x0 (rN.ws.take x0.2.2.length) true false)] := by
      rw [← hx0n]; rfl
    have e2 : (pieceRecs rN false (x0 :: rest) (cutWs ((x0 :: rest).map (·.2.2)) rN.ws) true).drop 1
        = pieceRecs rN false rest (cutWs (rest.map (·.2.2)) (rN.ws.drop x0.2.2.length)) false := rfl
    have hdrop := pieceRecs_drop_fst rN (x0 :: rest)
    rw [e1] at hA
    rw [e1, e2] at hB hC hD
    rw [e2] at hdrop
    icases Hback $$ %([(n, splitRec rN x0 (rN.ws.take x0.2.2.length) true false)] : List (Loc × NRec))
      %(pieceRecs rN false rest (cutWs (rest.map (·.2.2)) (rN.ws.drop x0.2.2.length)) false ++
        [(pl, newParRec pv' ((x0 :: rest).map (·.1)))]) [] [HN] [Hbo] [Htf] [Hrf] [HT HP]
      with ⟨%Hfresh, Hh⟩
    · ipureintro; exact ⟨hA, hB, hC⟩
    · iapply BigSepL.bigSepL_singleton.2
      simp only [decide_eq_true hlv]
      iexact HN
    · iexact Hbo
    · iexact Htf
    · iexact Hrf
    · iapply (BigSepL.bigSepL_append).2
      iframe
      iapply BigSepL.bigSepL_nil.2; iempintro
    have hrel := hD (fun x hx => by
        have hm : x.1 ∈ (pieceRecs rN false rest (cutWs (rest.map (·.2.2))
            (rN.ws.drop x0.2.2.length)) false).map (·.1) := by
          rw [hdrop]; exact List.mem_map.2 ⟨x, hx, rfl⟩
        obtain ⟨p, hp, e⟩ := List.mem_map.1 hm
        rw [← e]; exact Hfresh p (List.mem_append_left _ hp))
      (Hfresh _ (List.mem_append_right _ (List.mem_singleton_self _)))
    iexists _, _, pl, newParRec pv' ((x0 :: rest).map (·.1))
    isplitl [Hh Hfills Hdb Hst Hfr]
    · iapply (wtxW_frame K tx r m _).2
      rw [splitFr_splitX, splitX_handles]
      iframe
    ipureintro
    refine ⟨hrel, fun x hx => ?_⟩
    have := hfits x hx
    rw [w4096] at this
    exact ⟨this.1, fun _ => this.2⟩

end open_

end Spill

end bbolt
end EtcdGrove
end Perennial

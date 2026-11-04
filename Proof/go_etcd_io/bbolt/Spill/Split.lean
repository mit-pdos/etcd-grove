/-
`node.split` (U9a, `notes/bbolt-proof-plan.md`): unit-internal, stated and proved here over the same
resources as `node.splitTwo` (`Spill/SplitTwo`), which it calls until it does not split. The pieces
`xs` (location, struct, inodes) cover the node's inodes in order, every one fits a page
(`pieceFits`) and, split, holds at least two inodes (`piecesShape`); the first is the node itself,
the others fresh nodes of its bucket and kind, all under one parent (`parentAfter`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.SplitTwo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pieces
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- A piece after the first: a fresh node of `nv`'s bucket and kind under the parent `pl`, with
the inodes slice `s`. -/
def pieceStruct (nv : node) (pl : Loc) (s : GoSlice) : node :=
  { (zero_val node : node) with bucket' := nv.bucket', isLeaf' := nv.isLeaf', parent' := pl, inodes' := s }

/-- **The pieces of a split**: each fits a page and has at least two inodes; the first is the node
`nl` itself under `pl`, the others fresh nodes (`pieceStruct`). -/
def piecesShape (ps : Nat) (nl : Loc) (nv : node) (pl : Loc)
    (xs : List (Loc × node × List Inode)) : Prop :=
  (∀ x ∈ xs, pieceFits ps x.2.2 ∧ 2 ≤ x.2.2.length) ∧
  ∃ x0 rest, xs = x0 :: rest ∧ x0.1 = nl ∧ x0.2.1 = { nv with parent' := pl, inodes' := x0.2.1.inodes' } ∧
    ∀ x ∈ rest, x.1 ≠ null ∧ x.2.1 = pieceStruct nv pl x.2.1.inodes'

/-- **The parent after a split** into the nodes `ls`: a new one (`nv` had none) whose children are
`ls`, or `nv`'s, the pieces after the first appended to its children. -/
def parentAfter (nv pv : node) (pcs : List Loc) (pl : Loc) (pv' : node) (pcs' : List Loc)
    (ls : List Loc) : Prop :=
  (nv.parent' = null ∧ pv' = newParent nv pv'.children' ∧ pcs' = ls) ∨
  (nv.parent' ≠ null ∧ pl = nv.parent' ∧ pv' = { pv with children' := pv'.children' } ∧
    pcs' = pcs ++ ls.drop 1)

/-- `node.split`'s loop: before the first split (the node itself, its parent), or after it (the
pieces `done`, the current node `cl` a fresh one under the common parent). -/
def splitPhase (ps : Nat) (nl : Loc) (nv pv : node) (pcs : List Loc)
    (done : List (Loc × node × List Inode)) (cl : Loc) (cv : node) (rest : List Inode)
    (pvX : node) (pcsX : List Loc) : Prop :=
  (done = [] ∧ cl = nl ∧ cv = nv ∧ pvX = pv ∧ pcsX = pcs) ∨
  (cv.parent' ≠ null ∧ cl ≠ null ∧ cv = pieceStruct nv cv.parent' cv.inodes' ∧ 3 ≤ rest.length ∧
    piecesShape ps nl nv cv.parent' done ∧
    parentAfter nv pv pcs cv.parent' pvX pcsX ((done ++ [(cl, cv, rest)]).map (·.1)))

omit [GoGlobalContext] [GoSemanticsFunctions] in
theorem splitPhase_bucket {ps nl nv pv pcs done cl cv rest pvX pcsX}
    (h : splitPhase ps nl nv pv pcs done cl cv rest pvX pcsX) :
    cv.bucket' = nv.bucket' ∧ cv.isLeaf' = nv.isLeaf' := by
  rcases h with ⟨-, -, rfl, -⟩ | ⟨-, -, hc, -⟩
  · exact ⟨rfl, rfl⟩
  · rw [hc]; exact ⟨rfl, rfl⟩

/-- A split step of the loop. -/
theorem splitPhase_step {ps nl nv pv pcs done cl cv rest pvX pcsX} {k : Nat} {nx pl : Loc}
    {pv'' : node} {pcs'' : List Loc}
    (hP : splitPhase ps nl nv pv pcs done cl cv rest pvX pcsX) (hk2 : 2 ≤ k)
    (hk3 : k + 3 ≤ rest.length) (hfit : pieceFits ps (rest.take k)) (hnx : nx ≠ null)
    (hpl : pl ≠ null) (hsp : splitParent cl nx cv pvX pcsX pl pv'' pcs'') :
    splitPhase ps nl nv pv pcs (done ++ [(cl, splitLeft cv pl k, rest.take k)]) nx
      (splitRight cv pl k) (rest.drop k) pv'' pcs'' := by
  obtain ⟨hb, hl⟩ := splitPhase_bucket hP
  have hR : splitRight cv pl k = pieceStruct nv pl (inodesR cv k) := by
    simp only [splitRight, pieceStruct, hb, hl]
  have hlen : 3 ≤ (rest.drop k).length := by simp; omega
  have hnew : pieceFits ps (rest.take k) ∧ 2 ≤ (rest.take k).length := ⟨hfit, by simp; omega⟩
  right
  refine ⟨hpl, hnx, ?_, hlen, ?_, ?_⟩
  · rw [hR]; rfl
  · rcases hP with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨hpn, hcl, hc, -, ⟨hfits, x0, rest0, hd, hx0, hx0s, hrest⟩, -⟩
    · refine ⟨?_, (cl, splitLeft cv pl k, rest.take k), [], by simp, rfl, rfl, by simp⟩
      intro x hx; simp at hx; subst hx; exact hnew
    · have hplx : pl = cv.parent' := by
        rcases hsp with ⟨h, -⟩ | ⟨-, h, -⟩
        · exact absurd h hpn
        · exact h
      refine ⟨?_, x0, rest0 ++ [(cl, splitLeft cv pl k, rest.take k)], by rw [hd]; rfl, hx0, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hfits x hx
        · simp at hx; subst hx; exact hnew
      · simp only [splitRight] at *; rw [hplx]; exact hx0s
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · rw [hplx]; exact hrest x hx
        · simp at hx; subst hx
          refine ⟨hcl, ?_⟩
          simp only [splitLeft, splitRight]
          rw [hc]; simp only [pieceStruct]
  · simp only [splitRight]
    rcases hP with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨hpn, -, -, -, ⟨-, x0, rest0, hd, -⟩, hpa⟩
    · rcases hsp with ⟨h0, hpv, hpc⟩ | ⟨h0, hpl', hpv, hpc⟩
      · left; exact ⟨h0, hpv, by rw [hpc]; rfl⟩
      · right; exact ⟨h0, hpl', hpv, by rw [hpc]; rfl⟩
    · have hplx : pl = cv.parent' := by
        rcases hsp with ⟨h, -⟩ | ⟨-, h, -⟩
        · exact absurd h hpn
        · exact h
      rcases hsp with ⟨h, -⟩ | ⟨-, -, hpv, hpc⟩
      · exact absurd h hpn
      rw [← hplx] at hpa
      rcases hpa with ⟨h0, hpv0, hpc0⟩ | ⟨h0, hpl0, hpv0, hpc0⟩
      · left
        refine ⟨h0, ?_, ?_⟩
        · rw [hpv, hpv0]; rfl
        · rw [hpc, hpc0]; simp
      · right
        refine ⟨h0, hpl0, ?_, ?_⟩
        · rw [hpv, hpv0]
        · rw [hpc, hpc0, hd]; simp

omit [GoGlobalContext] [GoSemanticsFunctions] in
/-- The loop's end: the current node did not split. -/
theorem splitPhase_final {ps nl nv pv pcs done cl cv rest pvX pcsX} {ins : List Inode}
    (hP : splitPhase ps nl nv pv pcs done cl cv rest pvX pcsX)
    (hfl : (done.map (·.2.2)).flatten ++ rest = ins) (hfit : pieceFits ps rest) :
    (done = [] ∧ cl = nl ∧ cv = nv ∧ rest = ins ∧ pvX = pv ∧ pcsX = pcs) ∨
    (2 ≤ (done ++ [(cl, cv, rest)]).length ∧ cv.parent' ≠ null ∧
      piecesShape ps nl nv cv.parent' (done ++ [(cl, cv, rest)]) ∧
      parentAfter nv pv pcs cv.parent' pvX pcsX ((done ++ [(cl, cv, rest)]).map (·.1))) := by
  rcases hP with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨hpn, hcl, hc, h3, ⟨hfits, x0, rest0, hd, hx0, hx0s, hrest⟩, hpa⟩
  · left; simp at hfl; exact ⟨rfl, rfl, rfl, hfl, rfl, rfl⟩
  · right
    refine ⟨by rw [hd]; simp, hpn, ⟨?_, x0, rest0 ++ [(cl, cv, rest)], by rw [hd]; rfl, hx0, hx0s, ?_⟩, hpa⟩
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hfits x hx
      · simp at hx; subst hx; exact ⟨hfit, by simp; omega⟩
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hrest x hx
      · simp at hx; subst hx; exact ⟨hcl, hc⟩

end pieces

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`n.split(ps)`** (`ps < 2 ^ 53`, the bucket's fill percent not a NaN): the pieces `xs`, returned
as a slice of their locations, cover the inodes in order. Unsplit, the node as it was (and it
fits); split, the pieces' points-tos (`piecesShape`), under the parent `pl` (`parentAfter`). -/
abbrev node.split.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp)
    (nl : Loc) (nv : node) (ins : List Inode) (f : w64) (dqf dqt : DFrac)
    (pv : node) (pcs : List Loc) (ps : w64),
  insSize ins < 2 ^ 63 → ¬ float64IsNaN f → uint.Z ps < 2 ^ 53 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ K.core ∗ reg tx K.B r ∗
      statsTok r m q ∗
      nl ↦ nv ∗ nv.inodes' ↦* ins ∗ ownSliceCap Inode nv.inodes' (DFrac.own 1) ∗
      nv.bucket'.[Bucket, go!"FillPercent"] ↦{dqf} f ∗ nv.bucket'.[Bucket, go!"tx"] ↦{dqt} tx ∗
      parentOwn nv.parent' pv pcs }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"split")) (Val #ps))
  {{ (s : GoSlice) (xs : List (Loc × node × List Inode)), RET #s;
      statsTok r m q ∗
      nv.bucket'.[Bucket, go!"FillPercent"] ↦{dqf} f ∗ nv.bucket'.[Bucket, go!"tx"] ↦{dqt} tx ∗
      s ↦* xs.map (·.1) ∗ ⌜(xs.map (·.2.2)).flatten = ins⌝ ∗
      ((⌜xs = [(nl, nv, ins)] ∧ pieceFits ps.toNat ins⌝ ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗
          ownSliceCap Inode nv.inodes' (DFrac.own 1) ∗ parentOwn nv.parent' pv pcs) ∨
        (∃ (pl : Loc) (pv' : node) (pcs' : List Loc),
          ⌜2 ≤ xs.length ∧ pl ≠ null ∧ piecesShape ps.toNat nl nv pl xs ∧
            parentAfter nv pv pcs pl pv' pcs' (xs.map (·.1))⌝ ∗
          ([∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ x.2.1.inodes' ↦* x.2.2) ∗
          pl ↦ pv' ∗ pv'.children' ↦* pcs' ∗ ownSliceCap Loc pv'.children' (DFrac.own 1))) }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
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
  have Hrest : insSize rest ≤ insSize ins := by
    rw [← Hph.2]
    have := insSize_append ((done.map (·.2.2)).flatten) rest
    have : 16 ≤ insSize ((done.map (·.2.2)).flatten) := by rw [insSize_eq]; omega
    omega
  rw [← hb]
  try wp_auto
  wp_apply node.splitTwo.wp_proof hK hV hInc K tx r m q cl cv rest f dqf dqt pvX pcsX ps
    (by omega) Hnan Hps $$ [Hst Hc Hci Hcc Hfp Htx Hpar] as %nx ⟨Hst, Hfp, Htx, Hpost⟩
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

/-
The pieces, phases and spec of `node.split`, out of `Split.lean`'s proof so that the spill modules
import them without the proof (import tiers, 2026-11-18).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.SplitTwoDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

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
  (∀ x ∈ xs, pieceFitFor x.2.1.isLeaf' ps x.2.2 ∧ pieceMin x.2.1.isLeaf' ≤ x.2.2.length) ∧
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
  (cv.parent' ≠ null ∧ cl ≠ null ∧ cv = pieceStruct nv cv.parent' cv.inodes' ∧ remainderMin cv.isLeaf' ≤ rest.length ∧
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
    (hP : splitPhase ps nl nv pv pcs done cl cv rest pvX pcsX) (hk2 : pieceMin cv.isLeaf' ≤ k)
    (hk3 : k + remainderMin cv.isLeaf' ≤ rest.length) (hfit : pieceFitFor cv.isLeaf' ps (rest.take k)) (hnx : nx ≠ null)
    (hpl : pl ≠ null) (hsp : splitParent cl nx cv pvX pcsX pl pv'' pcs'') :
    splitPhase ps nl nv pv pcs (done ++ [(cl, splitLeft cv pl k, rest.take k)]) nx
      (splitRight cv pl k) (rest.drop k) pv'' pcs'' := by
  obtain ⟨hb, hl⟩ := splitPhase_bucket hP
  have hR : splitRight cv pl k = pieceStruct nv pl (inodesR cv k) := by
    simp only [splitRight, pieceStruct, hb, hl]
  have hlen : remainderMin cv.isLeaf' ≤ (rest.drop k).length := by simp; omega
  have hnew : pieceFitFor cv.isLeaf' ps (rest.take k) ∧ pieceMin cv.isLeaf' ≤ (rest.take k).length := ⟨hfit, by simp; omega⟩
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
    (hfl : (done.map (·.2.2)).flatten ++ rest = ins) (hfit : pieceFitFor cv.isLeaf' ps rest) :
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
      · simp at hx; subst hx
        refine ⟨hfit, Nat.le_trans ?_ h3⟩
        change pieceMin cv.isLeaf' ≤ remainderMin cv.isLeaf'
        cases cv.isLeaf' <;> decide
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hrest x hx
      · simp at hx; subst hx; exact ⟨hcl, hc⟩

end pieces

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`n.split(ps)`** (`ps < 2 ^ 53`, every inode's share below `2 ^ 60` (`insBnd`), the bucket's fill percent not a NaN): the pieces `xs`, returned
as a slice of their locations, cover the inodes in order. Unsplit, the node as it was (and it
fits); split, the pieces' points-tos (`piecesShape`), under the parent `pl` (`parentAfter`). -/
abbrev node.split.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp)
    (nl : Loc) (nv : node) (ins : List Inode) (f : w64) (dqf dqt : DFrac)
    (pv : node) (pcs : List Loc) (ps : w64),
  insBnd ins → ¬ float64IsNaN f → uint.Z ps < 2 ^ 53 →
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
      ((⌜xs = [(nl, nv, ins)] ∧ pieceFitFor nv.isLeaf' ps.toNat ins⌝ ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗
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
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

end proof

end bbolt
end EtcdGrove
end Perennial

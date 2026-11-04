/-
`node.splitTwo` (U9a, `notes/bbolt-proof-plan.md`; ported from `old/bbolt/`'s `WriteSplit` and
`node__splitTwo`): unit-internal, stated and proved here over the node's points-tos, its parent's
(`parentOwn`), its bucket's `FillPercent` and `tx` fields and the statistics' token. A split
leaves the node its first `k` inodes without their capacity (the rest of the array is `next`'s),
and both pieces fit a page (`pieceFits`): what `node.write`'s premises need.
-/
module

public import Spec.go_etcd_io.bbolt.TxStats__IncSplit
public import Proof.go_etcd_io.bbolt.Spill.SplitIndex
public import Proof.go_etcd_io.bbolt.Spill.SplitThreshold

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section nodes
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The first piece's inodes: the old slice's first `k`. -/
def inodesL (nv : node) (k : Nat) : GoSlice :=
  slice.slice nv.inodes' Inode (W64 0) (W64 (k : Int))

/-- The second piece's inodes: the rest of the old slice (and its capacity). -/
def inodesR (nv : node) (k : Nat) : GoSlice :=
  slice.slice nv.inodes' Inode (W64 (k : Int)) nv.inodes'.len

/-- The node after the split: its first `k` inodes, under the parent `pl`. -/
def splitLeft (nv : node) (pl : Loc) (k : Nat) : node :=
  { nv with parent' := pl, inodes' := inodesL nv k }

/-- The new node `next`: the other inodes, under the parent `pl`. -/
def splitRight (nv : node) (pl : Loc) (k : Nat) : node :=
  { (zero_val node : node) with bucket' := nv.bucket', isLeaf' := nv.isLeaf', parent' := pl, inodes' := inodesR nv k }

/-- A new parent: the node's bucket, the children `cs`. -/
def newParent (nv : node) (cs : GoSlice) : node :=
  { (zero_val node : node) with bucket' := nv.bucket', children' := cs }

/-- The parent after the split of `nl` (struct `nv`; its parent `pv`, children `pcs`) into it and
`nx`: the old one with `nx` appended to its children, or a new one whose children are the two. -/
def splitParent (nl nx : Loc) (nv pv : node) (pcs : List Loc) (pl : Loc) (pv' : node)
    (pcs' : List Loc) : Prop :=
  (nv.parent' = null ∧ pv' = newParent nv pv'.children' ∧ pcs' = [nl, nx]) ∨
  (nv.parent' ≠ null ∧ pl = nv.parent' ∧ pv' = { pv with children' := pv'.children' } ∧
    pcs' = pcs ++ [nx])

end nodes

section own
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A node's parent `p` (if any): its struct and its children with their capacity. -/
def parentOwn (p : Loc) (pv : node) (pcs : List Loc) : IProp GF :=
  if p = null then iprop(emp) else
    iprop(p ↦ pv ∗ pv.children' ↦* pcs ∗ ownSliceCap Loc pv.children' (DFrac.own 1))

end own

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`n.splitTwo(ps)`** (`ps < 2 ^ 53`, every inode's share below `2 ^ 60` (`insBnd`), the bucket's fill percent not a NaN). Unsplit (`nil`),
everything as it was, and the node fits (`pieceFits ps`). Split at `k`: the node keeps its first
`k` inodes (`splitLeft`), a new node `nx` the rest with the capacity (`splitRight`), both under
the parent `pl` (`splitParent`), the first piece fitting; the split counted. -/
abbrev node.splitTwo.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp)
    (nl : Loc) (nv : node) (ins : List Inode) (f : w64) (dqf dqt : DFrac)
    (pv : node) (pcs : List Loc) (ps : w64),
  insBnd ins → ¬ float64IsNaN f → uint.Z ps < 2 ^ 53 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ K.core ∗ reg tx K.B r ∗
      statsTok r m q ∗
      nl ↦ nv ∗ nv.inodes' ↦* ins ∗ ownSliceCap Inode nv.inodes' (DFrac.own 1) ∗
      nv.bucket'.[Bucket, go!"FillPercent"] ↦{dqf} f ∗ nv.bucket'.[Bucket, go!"tx"] ↦{dqt} tx ∗
      parentOwn nv.parent' pv pcs }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"splitTwo")) (Val #ps))
  {{ (nx : Loc), RET (PairV #nl #nx);
      statsTok r m q ∗
      nv.bucket'.[Bucket, go!"FillPercent"] ↦{dqf} f ∗ nv.bucket'.[Bucket, go!"tx"] ↦{dqt} tx ∗
      ((⌜nx = null ∧ pieceFits ps.toNat ins⌝ ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗
          ownSliceCap Inode nv.inodes' (DFrac.own 1) ∗ parentOwn nv.parent' pv pcs) ∨
        (∃ (k : Nat) (pl : Loc) (pv' : node) (pcs' : List Loc),
          ⌜2 ≤ k ∧ k + 3 ≤ ins.length ∧ pieceFits ps.toNat (ins.take k) ∧ nx ≠ null ∧ pl ≠ null ∧
            splitParent nl nx nv pv pcs pl pv' pcs'⌝ ∗
          nl ↦ splitLeft nv pl k ∗ inodesL nv k ↦* ins.take k ∗
          nx ↦ splitRight nv pl k ∗ inodesR nv k ↦* ins.drop k ∗
          ownSliceCap Inode (inodesR nv k) (DFrac.own 1) ∗
          pl ↦ pv' ∗ pv'.children' ↦* pcs' ∗ ownSliceCap Loc pv'.children' (DFrac.own 1))) }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem node.splitTwo.wp_proof (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hV : internal.common.Inode.Value.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncSplit.spec (GF := GF) (hG := hG)) :
    node.splitTwo.spec (GF := GF) (hG := hG) := by
  intro K tx r m q nl nv ins f dqf dqt pv pcs ps Hbnd Hnan Hps
  wp_start as ⟨Hcore, Hreg, Hst, Hn, Hins, Hcap, Hfp, Htx, Hpar⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hins
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  try wp_auto
  have Hlen : ins.length < 2 ^ 63 := by rw [Hl.1]; word
  by_cases h4 : sint.Z nv.inodes'.len ≤ sint.Z (W64 4)
  · rw [decide_eq_true h4]
    try wp_auto
    ihave Hn : (nl ↦ nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    iapply HΦ
    iframe
    ileft
    iframe
    ipureintro
    exact ⟨rfl, pieceFits_unsplit _ _ (Or.inl (by rw [Hl.1]; word))⟩
  rw [decide_eq_false h4]
  try wp_auto
  ihave Hn : (nl ↦ nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_apply node.sizeLessThan.wp_proof hK hV nl nv ins (DFrac.own 1) (DFrac.own 1) ps Hbnd
    (by omega) $$ [Hn Hins]
    as ⟨Hn, Hins⟩
  · iframe
  by_cases hs : decide (ins = [] ∨ insSize ins < ps.toNat) = true
  · rw [hs]
    try wp_auto
    iapply HΦ
    iframe
    ileft
    iframe
    ipureintro
    exact ⟨rfl, pieceFits_unsplit _ _ (Or.inr (by simpa using hs))⟩
  rw [Bool.not_eq_true] at hs
  rw [hs]
  try wp_auto
  wp_apply splitThreshold.wp_proof ps f Hnan Hps as %t %Ht
  try wp_auto
  wp_apply node.splitIndex.wp_proof hK hV nl nv ins (DFrac.own 1) (DFrac.own 1) t Hbnd Ht.1
    (by omega) $$ [Hn Hins]
    as ⟨Hn, Hins⟩
  · iframe
  have H5 : 5 ≤ ins.length := by rw [Hl.1]; word
  obtain ⟨hk2, hk3, hk⟩ := splitIdx_spec (sint.nat t) ins H5
  generalize Hk : (splitIdx (sint.nat t) ins).1 = k at hk2 hk3 hk
  try wp_auto
  wp_join iprop(n_ptr ↦ nl ∗ ∃ (pl : Loc) (pv0 : node) (pcs0 : List Loc),
      nl ↦ ({ nv with parent' := pl } : node) ∗ pl ↦ pv0 ∗ pv0.children' ↦* pcs0 ∗
      ownSliceCap Loc pv0.children' (DFrac.own 1) ∗
      ⌜pl ≠ null ∧ ((nv.parent' = null ∧ pv0 = newParent nv pv0.children' ∧ pcs0 = [nl]) ∨
        (nv.parent' ≠ null ∧ pl = nv.parent' ∧ pv0 = pv ∧ pcs0 = pcs))⌝)
    at next with [n Hn Hpar] as ⟨n, %pl, %pv0, %pcs0, Hn, Hpl, Hpcs, Hpcap, %Hpl0⟩
  · by_cases hp : nv.parent' = null
    · rw [decide_eq_true hp]
      try wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, Hslcap⟩
      try wp_auto
      icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hr0, %Hnn'⟩
      isplitl []
      · ipureintro; rfl
      iframe
      ipureintro
      exact ⟨Hnn', Or.inl ⟨hp, rfl, rfl⟩⟩
    · rw [decide_eq_false hp]
      try wp_auto
      isimp only [parentOwn, hp, ↓reduceIte] at Hpar
      icases Hpar with ⟨Hp, Hpc, Hpcap⟩
      isplitl []
      · ipureintro; rfl
      iframe
      ipureintro
      exact ⟨hp, Or.inr ⟨hp, rfl, rfl, rfl⟩⟩
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  wp_apply wp_slice_append $$ [$Hpcs $Hpcap $Hsl2] as %s' ⟨Hpcs, Hpcap, -⟩
  try wp_auto
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  have hkz : sint.Z (W64 (k : Int)) = k := by have := Hl.1; word
  have hz0 : sint.Z (W64 0) = 0 := by word
  have hLZ : (ins.length : Int) = sint.Z nv.inodes'.len := by rw [Hl.1]; word
  rw [if_pos (by omega)]
  try wp_auto
  rw [if_pos (by omega)]
  try wp_auto
  wp_apply hInc K tx r m q (W64 1) $$ [Hcore Hreg Hst] as %st' Hst
  · iframe
  try wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hr0, %Hnn'⟩
  have hkk : sint.nat (W64 (k : Int)) = k := by word
  ihave Hins := (ownSlice_split_all (W64 (k : Int)) nv.inodes' (DFrac.own 1) ins
    ⟨by omega, by omega⟩).1 $$ Hins
  rw [hkk]
  icases Hins with ⟨HL, HR⟩
  ihave Hcap := (ownSliceCap_slice nv.inodes' (W64 (k : Int)) (DFrac.own 1)
    ⟨by omega, by omega, Hcw.2⟩).1 $$ Hcap
  iapply HΦ
  iframe
  iright
  iexists k, pl, ({ pv0 with children' := s' } : node), pcs0 ++ [«$r0_ptr»]
  isplitr
  · ipureintro
    refine ⟨hk2, hk3, ?_, Hnn', Hpl0.1, ?_⟩
    · rw [← Hk]; exact pieceFits_split _ _ ins H5 (by have := Ht.2; unfold uint.Z at this; word)
    rcases Hpl0.2 with ⟨hp, hpv, hpc⟩ | ⟨hp, hpl, hpv, hpc⟩
    · refine Or.inl ⟨hp, ?_, by rw [hpc]; rfl⟩
      rw [hpv]; rfl
    · exact Or.inr ⟨hp, hpl, by rw [hpv], by rw [hpc]⟩
  simp only [splitLeft, splitRight, inodesL, inodesR]
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial

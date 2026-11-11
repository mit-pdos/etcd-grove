/-
`node.pageElementSize`, `node.sizeLessThan` and `node.splitIndex` (U9a, `notes/bbolt-proof-plan.md`):
unit-internal functions of the spill, stated and proved here over the node's points-to and its
inodes slice (only the slices' headers are read), with `Spill/SplitModel`'s model.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Value
public import Proof.go_etcd_io.bbolt.Spill.SplitModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `n.pageElementSize()`: 16, for a leaf as for a branch. -/
abbrev node.pageElementSize.spec : Prop :=
  ∀ (n : Loc) (nv : node) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ n ↦{dq} nv }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"pageElementSize")) (Val #()))
  {{ RET #(W64 16); n ↦{dq} nv }}

/-- `n.sizeLessThan(v)`: whether the node is empty or its page (`insSize`) is below `v`
(every inode's share below `2 ^ 60` and `v` below `2 ^ 62`: the running size, which stops once
past `v`, does not wrap). -/
abbrev node.sizeLessThan.spec : Prop :=
  ∀ (n : Loc) (nv : node) (ins : List Inode) (dq dqi : DFrac) (v : w64),
  insBnd ins → uint.Z v < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ n ↦{dq} nv ∗ nv.inodes' ↦*{dqi} ins }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"sizeLessThan")) (Val #v))
  {{ RET #(decide (ins = [] ∨ insSize ins < v.toNat)); n ↦{dq} nv ∗ nv.inodes' ↦*{dqi} ins }}

/-- `n.splitIndex(t)` with a threshold in `[0, 2 ^ 62)`: `splitIdx`'s index and size (every
inode's share below `2 ^ 60`: past the first two inodes the running size stays below `t`). -/
abbrev node.splitIndex.spec : Prop :=
  ∀ (n : Loc) (nv : node) (ins : List Inode) (dq dqi : DFrac) (t : w64),
  insBnd ins → 0 ≤ sint.Z t → sint.Z t < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ n ↦{dq} nv ∗ nv.inodes' ↦*{dqi} ins }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"splitIndex")) (Val #t))
  {{ RET (PairV #(W64 ((splitIdx (sint.nat t) ins).1 : Int)) #(W64 ((splitIdx (sint.nat t) ins).2 : Int)));
      n ↦{dq} nv ∗ nv.inodes' ↦*{dqi} ins }}

end spec

private theorem splitGo_step [GooseExts] (t L j idx sz : Nat) (ins : List Inode) (it : Inode)
    (hj : j < L) (hL : L ≤ ins.length) (h : ins[j]? = some it) :
    splitGo t j idx sz ((ins.take L).drop j) =
      if 2 ≤ j ∧ t < sz + inSz it then (j, sz)
      else splitGo t (j + 1) j (sz + inSz it) ((ins.take L).drop (j + 1)) := by
  have hiL : j < (ins.take L).length := by simp; omega
  rw [List.drop_eq_getElem_cons hiL]
  have : (ins.take L)[j] = it := by
    rw [List.getElem_take]; exact (List.getElem?_eq_some_iff.1 h).2
  rw [this]; rfl

theorem uintZ_W64_nat (x : Nat) (h : x < 2 ^ 64) : uint.Z (W64 (x : Int)) = (x : Int) := by
  word

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem node.pageElementSize.wp_proof : node.pageElementSize.spec (GF := GF) (hG := hG) := by
  intro nl nv dq
  wp_start as Hn
  try unfold internal.common.BranchPageElementSize
  try unfold internal.common.LeafPageElementSize
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  wp_auto
  ihave Hn : (nl ↦{dq} nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  cases h : nv.isLeaf' <;> (try simp only [Bool.false_eq_true, ↓reduceIte]) <;> wp_auto <;>
    iapply HΦ <;> iframe

theorem node.sizeLessThan.wp_proof (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hV : internal.common.Inode.Value.spec (GF := GF) (hG := hG)) :
    node.sizeLessThan.spec (GF := GF) (hG := hG) := by
  intro nl nv ins dq dqs v Hbnd Hv
  wp_start as ⟨Hn, Hs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  wp_auto
  wp_apply node.pageElementSize.wp_proof $$ [$Hn] as Hn
  try wp_auto
  try unfold internal.common.PageHeaderSize
  try wp_auto
  ihave IH : (∃ (j : w64),
      "i" ∷ i_ptr ↦ j ∗ "sz" ∷ sz_ptr ↦ W64 (insSize (ins.take (sint.nat j)) : Int) ∗
      "Hs" ∷ nv.inodes' ↦*{dqs} ins ∗ "Hn" ∷ nl ↦{dq} nv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z nv.inodes'.len ∧
        (0 < sint.nat j → insSize (ins.take (sint.nat j)) < v.toNat)⌝ : IProp GF) $$ [i sz Hs Hn]
  · iexists W64 0
    simp only [named]
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    ipureintro; refine ⟨by word, by word, fun h => absurd h (by decide)⟩
  wp_for IH
  iStructNamed Hn
  wp_auto
  ihave Hn : (nl ↦{dq} nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z nv.inodes'.len := by
      refine Classical.byContradiction fun h => ?_; simp [h, false_neq_true] at Hif
    have Hjn : sint.nat j < ins.length := by rw [Hsl.1]; word
    iStructNamed Hn
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj.1, Hlt⟩)]
    list_elem ins (sint.Z j).toNat as it
    icases ownSlice_elem_acc (sint.Z j) it _ _ ins Hj.1 Hit_lookup $$ Hs with ⟨Hit, Hsback⟩
    try wp_auto
    ihave Hn : (nl ↦{dq} nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    wp_apply hK $$ [$Hit] as Hit
    try wp_auto
    wp_apply hV $$ [$Hit] as Hit
    try wp_auto
    ihave Hs := Hsback $$ Hit
    rw [list_set_lookup_self _ _ _ Hit_lookup]
    have Htk : ins.take (sint.nat j + 1) = ins.take (sint.nat j) ++ [it] := by
      rw [List.take_add_one, show sint.nat j = (sint.Z j).toNat from rfl, Hit_lookup]; rfl
    have Hnext : insSize (ins.take (sint.nat j + 1)) = insSize (ins.take (sint.nat j)) + inSz it := by
      rw [Htk, insSize_snoc]
    have Hle : insSize (ins.take (sint.nat j + 1)) ≤ insSize ins := insSize_take_le _ _
    have Hlt63 : insSize (ins.take (sint.nat j + 1)) < 2 ^ 63 := by
      have hit : inSz it < 2 ^ 60 := Hbnd it (List.mem_of_getElem? Hit_lookup)
      have hv : v.toNat < 2 ^ 62 := by unfold uint.Z at Hv; omega
      rcases Nat.eq_zero_or_pos (sint.nat j) with h0 | h0
      · rw [Hnext, h0, List.take_zero, insSize_nil]; omega
      · have := Hj.2.2 h0; rw [Hnext]; omega
    have Hsz : W64 (insSize (ins.take (sint.nat j)) : Int) + (W64 16 + it.key'.len + it.value'.len) =
        W64 (insSize (ins.take (sint.nat j + 1)) : Int) := by
      rw [Hnext]; unfold inSz; word
    rw [Hsz]
    have H64 : insSize (ins.take (sint.nat j + 1)) < 2 ^ 64 := by omega
    wp_if_destruct
    · have Hge : v.toNat ≤ insSize (ins.take (sint.nat j + 1)) := by
        rw [uintZ_W64_nat _ H64] at Hif; unfold uint.Z at Hif; omega
      have Hres : decide (ins = [] ∨ insSize ins < v.toNat) = false := by
        have : ins ≠ [] := by intro h; subst h; simp at Hjn
        simp only [decide_eq_false_iff_not, not_or]; exact ⟨this, by omega⟩
      wp_for_post
      try wp_auto
      rw [Hres]
      iapply HΦ; iframe
    · wp_for_post
      iframe
      iexists j + W64 1
      iframe
      have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      rw [Hj1]
      iframe
      ipureintro
      refine ⟨by word, by word, fun _ => ?_⟩
      rw [uintZ_W64_nat _ H64] at Hif; unfold uint.Z at Hif; omega
  · have Hge : ¬ sint.Z j < sint.Z nv.inodes'.len := by
      intro h; simp [h] at Hif
    simp only [Hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    have Heq : sint.nat j = ins.length := by rw [Hsl.1]; word
    try wp_auto
    rw [Heq, List.take_length] at Hj
    have Hres : decide (ins = [] ∨ insSize ins < v.toNat) = true := by
      rcases Nat.eq_zero_or_pos ins.length with h | h
      · simp [List.eq_nil_of_length_eq_zero h]
      · simp only [decide_eq_true_eq]; exact Or.inr (Hj.2.2 h)
    rw [Hres]
    iapply HΦ; iframe

theorem node.splitIndex.wp_proof (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hV : internal.common.Inode.Value.spec (GF := GF) (hG := hG)) :
    node.splitIndex.spec (GF := GF) (hG := hG) := by
  intro nl nv ins dq dqs thr Hbnd Hthr Hthr'
  wp_start as ⟨Hn, Hs⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  try unfold internal.common.PageHeaderSize
  try unfold internal.common.MinKeysPerPage
  wp_auto
  ihave IH : (∃ (j idx : w64) (sz : Nat),
      "i" ∷ i_ptr ↦ j ∗ "index" ∷ index_ptr ↦ idx ∗ "sz" ∷ sz_ptr ↦ W64 (sz : Int) ∗
      "Hs" ∷ nv.inodes' ↦*{dqs} ins ∗ "Hn" ∷ nl ↦{dq} nv ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ ins.length - 2 ∧ idx.toNat ≤ sint.nat j ∧
        sz = insSize (ins.take (sint.nat j)) ∧
        splitGo (sint.nat thr) (sint.nat j) idx.toNat sz ((ins.take (ins.length - 2)).drop (sint.nat j)) =
          splitIdx (sint.nat thr) ins ∧ (2 < sint.nat j → sz ≤ sint.nat thr)⌝ : IProp GF)
      $$ [i index sz Hs Hn]
  · iexists W64 0, W64 0, 16
    simp only [named]
    iframe
    ipureintro
    refine ⟨by word, by word, by word, ?_, rfl, fun h => absurd h (by decide)⟩
    rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]; rfl
  wp_for IH
  iStructNamed Hn
  wp_auto
  ihave Hn : (nl ↦{dq} nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  have HL : sint.Z (nv.inodes'.len - W64 2) = sint.Z nv.inodes'.len - 2 ∨ sint.Z nv.inodes'.len < 2 := by
    rcases Int.lt_or_le (sint.Z nv.inodes'.len) 2 with h | h
    · exact Or.inr h
    · left; have : ins.length < 2 ^ 63 := by rw [Hsl.1]; word
      word
  wp_if_destruct
  · have Hlt : sint.Z j < sint.Z (nv.inodes'.len - W64 2) := by
      rcases Decidable.em (sint.Z j < sint.Z (nv.inodes'.len - W64 2)) with h | h
      · exact h
      · exfalso; rw [decide_eq_false h] at Hif; exact false_neq_true Hif
    have HjL : sint.nat j < ins.length - 2 := by
      rcases HL with h | h
      · rw [h] at Hlt; rw [Hsl.1]; word
      · exfalso; have : sint.Z (nv.inodes'.len - W64 2) < 0 := by word
        omega
    have Hjn : sint.nat j < ins.length := by omega
    iStructNamed Hn
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z nv.inodes'.len by
      constructor <;> word))]
    list_elem ins (sint.Z j).toNat as it
    wp_apply wp_load_slice_index _ (sint.Z j) ins _ it Hj.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hit_lookup
    try wp_auto
    ihave Hn : (nl ↦{dq} nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    wp_apply node.pageElementSize.wp_proof $$ [$Hn] as Hn
    try wp_auto
    wp_apply hK $$ [$inode] as inode
    try wp_auto
    wp_apply hV $$ [$inode] as inode
    try wp_auto
    have Hit_lookup' : ins[sint.nat j]? = some it := Hit_lookup
    have Hnext : insSize (ins.take (sint.nat j + 1)) = insSize (ins.take (sint.nat j)) + inSz it := by
      rw [List.take_add_one, Hit_lookup', Option.toList_some, insSize_snoc]
    have H64 : sz + inSz it < 2 ^ 63 := by
      have hit : inSz it < 2 ^ 60 := Hbnd it (List.mem_of_getElem? Hit_lookup')
      have ht : sint.nat thr < 2 ^ 62 := by rw [show sint.nat thr = (sint.Z thr).toNat from rfl]; omega
      by_cases h2 : sint.nat j ≤ 2
      · have := insSize_le_len (insBnd_take Hbnd (sint.nat j))
        have hl : (ins.take (sint.nat j)).length ≤ 2 := by simp; omega
        have : (ins.take (sint.nat j)).length * 2 ^ 60 ≤ 2 * 2 ^ 60 := Nat.mul_le_mul_right _ hl
        rw [Hj.2.2.2.1]; omega
      · have := Hj.2.2.2.2.2 (by omega); omega
    have Hsz : W64 (sz : Int) + (W64 16 + it.key'.len + it.value'.len) = W64 ((sz + inSz it : Nat) : Int) := by
      unfold inSz; word
    wp_if_destruct
    · try wp_auto
      rw [Hsz]
      wp_if_destruct
      · have Hc : 2 ≤ sint.nat j ∧ sint.nat thr < sz + inSz it := by
          constructor
          · word
          · rw [uintZ_W64_nat _ (by omega)] at Hif; unfold uint.Z at Hif; word
        wp_for_post
        try wp_auto
        rw [← Hj.2.2.2.2.1, splitGo_step _ _ _ _ _ ins it HjL (by omega) Hit_lookup', if_pos Hc]
        simp only
        rw [show W64 ((sint.nat j : Nat) : Int) = j by word]
        iapply HΦ; iframe
      · have Hc : ¬ (2 ≤ sint.nat j ∧ sint.nat thr < sz + inSz it) := by
          intro ⟨_, h⟩; apply Hif; rw [uintZ_W64_nat _ (by omega)]; unfold uint.Z; word
        try wp_auto
        rw [Hsz]
        wp_for_post
        iframe
        iexists j + W64 1, j, sz + inSz it
        iframe
        have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
        rw [Hj1]
        iframe
        ipureintro
        refine ⟨by word, by omega, by word, by rw [Hnext, Hj.2.2.2.1], ?_, ?_⟩
        · rw [← Hj.2.2.2.2.1, splitGo_step _ _ _ _ _ ins it HjL (by omega) Hit_lookup', if_neg Hc,
            show j.toNat = sint.nat j by word]
        · intro h; exact Classical.byContradiction fun hc => Hc ⟨by omega, by omega⟩
    · have Hc : ¬ (2 ≤ sint.nat j ∧ sint.nat thr < sz + inSz it) := by
        intro ⟨h, _⟩; apply Hif; word
      try wp_auto
      rw [Hsz]
      wp_for_post
      iframe
      iexists j + W64 1, j, sz + inSz it
      iframe
      have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      rw [Hj1]
      iframe
      ipureintro
      refine ⟨by word, by omega, by word, by rw [Hnext, Hj.2.2.2.1], ?_, ?_⟩
      · rw [← Hj.2.2.2.2.1, splitGo_step _ _ _ _ _ ins it HjL (by omega) Hit_lookup', if_neg Hc,
          show j.toNat = sint.nat j by word]
      · intro h; exact Classical.byContradiction fun hc => Hc ⟨by omega, by omega⟩
  · have Hge : ¬ sint.Z j < sint.Z (nv.inodes'.len - W64 2) := by
      intro h; rw [decide_eq_true h] at Hif; exact Hif rfl
    simp only [Hge, decide_false, Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    have HjL : sint.nat j = ins.length - 2 := by
      rcases HL with h | h
      · rw [h] at Hge; rw [Hsl.1] at Hj ⊢; word
      · rw [Hsl.1] at Hj ⊢; word
    have Hres := Hj.2.2.2.2.1
    rw [HjL, List.drop_eq_nil_of_le (by simp)] at Hres
    simp only [splitGo] at Hres
    rw [← Hres]
    simp only
    rw [show W64 ((idx.toNat : Nat) : Int) = idx by word]
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial

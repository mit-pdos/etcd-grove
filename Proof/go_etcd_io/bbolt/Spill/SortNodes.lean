/-
`sort.Sort(n.children)` in `node.spill` (U9d, `notes/bbolt-proof-plan.md`): the `nodes` slice
type (`Len`, `Less`, `Swap`; `Less` compares the children's first keys with `bytes.Compare`) is a
`sort.Interface` (`sorterSpec`, `Spec/sort/Sort.lean`) over the list of node locations in the
slice, ordered by their first keys `fk`.

The sorter's resource is the slice's points-to and a frame `Q` the nodes' first keys are read
from (the writer's heap and view in `node.spill`), through two accessors: a node's struct and
inodes (`Less` calls `inodes[0].Key()` on both nodes in turn), and two nodes' key bytes at once
(`bytes.Compare`; the same node twice when `i = j`). The key slices are a fixed function `ks` of
the node, so that the accessors' wands give back `Q` unchanged.
-/
module

public import Spec.sort.Sort
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Perennial.Spec.bytes.Compare
public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A `nodes` sorter's state** for the list `l`: the slice `s` holds `l`, every element `P`, and
the frame `Q`. -/
def nodesR (s : GoSlice) (P : Loc → Prop) (Q : IProp GF) (l : List Loc) : IProp GF :=
  iprop(s ↦* l ∗ ⌜∀ c ∈ l, P c⌝ ∗ Q)

/-- **The node `c`'s struct and inodes, out of `Q`**: its first inode's key slice is `ks c`. -/
def nodeHdAcc (Q : IProp GF) (ks : Loc → GoSlice) (c : Loc) : IProp GF :=
  iprop(∃ (dq : DFrac) (cv : node) (ins : List Inode) (it : Inode),
    ⌜ins[0]? = some it ∧ it.key' = ks c⌝ ∗ c ↦{dq} cv ∗ cv.inodes' ↦*{dq} ins ∗
    (c ↦{dq} cv ∗ cv.inodes' ↦*{dq} ins -∗ Q))

/-- **Two nodes' first keys' bytes, out of `Q`** (the same node twice when `c = d`). -/
def keyPairAcc (Q : IProp GF) (ks : Loc → GoSlice) (fk : Loc → List w8) (c d : Loc) :
    IProp GF :=
  iprop(∃ (dq1 dq2 : DFrac), ks c ↦*{dq1} fk c ∗ ks d ↦*{dq2} fk d ∗
    (ks c ↦*{dq1} fk c ∗ ks d ↦*{dq2} fk d -∗ Q))

/-- **`nodes` is a `sort.Interface`** over the locations in the slice `s`, ordered by first keys
`fk`, given the accessors of `Q` for the elements (`P`). -/
theorem nodes_sorter (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hC : bytes.Compare.spec (GF := GF) (hG := hG))
    (s : GoSlice) (P : Loc → Prop) (Q : IProp GF) (ks : Loc → GoSlice) (fk : Loc → List w8)
    (hQ1 : ∀ c, P c → Q ⊢ nodeHdAcc Q ks c)
    (hQ2 : ∀ c d, P c → P d → Q ⊢ keyPairAcc Q ks fk c d) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ⊢
      sorterSpec (interface.mk nodes.ty #s) (nodesR s P Q)
        (fun a b => decide (go.GoStringLt (fk a) (fk b))) := by
  iintro #Hpkg
  unfold nodeHdAcc at hQ1
  unfold keyPairAcc at hQ2
  unfold sorterSpec nodesR
  isplitr
  · -- `Len`
    iintro !> %l
    iintro !> %Φ ⟨Hs, %HP, HQ⟩ HΦ
    wp_method_call
    wp_call
    wp_auto
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    have : s.len = W64 (l.length : Int) := by
      have h1 := Hl.1
      have h2 := Hl.2
      word
    rw [this]
    iapply HΦ
    iframe
    ipureintro; exact HP
  isplitr
  · -- `Less`
    iintro !> %l %i %j %a %b %Hij
    iintro !> %Φ ⟨Hs, %HP, HQ⟩ HΦ
    obtain ⟨hi, hj, ha, hb⟩ := Hij
    have hPa := HP a (List.mem_of_getElem? ha)
    have hPb := HP b (List.mem_of_getElem? hb)
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    have hilt : sint.nat i < l.length := (List.getElem?_eq_some_iff.1 ha).1
    have hjlt : sint.nat j < l.length := (List.getElem?_eq_some_iff.1 hb).1
    have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := by
      have := Hl.1; refine ⟨hi, ?_⟩; word
    have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := by
      have := Hl.1; refine ⟨hj, ?_⟩; word
    wp_method_call
    wp_call
    wp_auto
    simp only [Hbi, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index s (sint.Z i) l (DFrac.own 1) a hi $$ [Hs] as Hs
    · iframe; ipureintro; exact ha
    icases hQ1 a hPa $$ HQ with ⟨%dqa, %cva, %insa, %ita, %Ha, Hna, Hia, HQa⟩
    ihave %Hla := ownSlice_len _ _ _ $$ Hia
    icases typedPointsto_not_null_dup _ _ _ $$ Hna with ⟨Hna, %Hnna⟩
    iStructNamed Hna
    wp_auto
    have Hba : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z cva.inodes'.len := by
      have : 0 < insa.length := by
        have := (List.getElem?_eq_some_iff.1 Ha.1).1; omega
      have := Hla.1; constructor <;> word
    simp only [Hba, _root_.and_self, ite_true]
    icases ownSlice_elem_acc (sint.Z (W64 0)) ita cva.inodes' dqa insa (by word)
      (by simpa using Ha.1) $$ Hia with ⟨Hita, Hiaback⟩
    wp_apply hK $$ [$Hita] as Hita
    try wp_auto
    ihave Hia := Hiaback $$ Hita
    ihave Hna : (a ↦{dqa} cva : IProp GF) $$
        [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnna
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    rw [list_set_lookup_self _ _ _ (by simpa using Ha.1)]
    ihave HQ := HQa $$ [$Hna $Hia]
    -- the second node
    simp only [Hbj, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index s (sint.Z j) l (DFrac.own 1) b hj $$ [Hs] as Hs
    · iframe; ipureintro; exact hb
    icases hQ1 b hPb $$ HQ with ⟨%dqb, %cvb, %insb, %itb, %Hb, Hnb, Hib, HQb⟩
    ihave %Hlb := ownSlice_len _ _ _ $$ Hib
    icases typedPointsto_not_null_dup _ _ _ $$ Hnb with ⟨Hnb, %Hnnb⟩
    iStructNamed Hnb
    wp_auto
    have Hbb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z cvb.inodes'.len := by
      have : 0 < insb.length := by
        have := (List.getElem?_eq_some_iff.1 Hb.1).1; omega
      have := Hlb.1; constructor <;> word
    simp only [Hbb, _root_.and_self, ite_true]
    icases ownSlice_elem_acc (sint.Z (W64 0)) itb cvb.inodes' dqb insb (by word)
      (by simpa using Hb.1) $$ Hib with ⟨Hitb, Hibback⟩
    wp_apply hK $$ [$Hitb] as Hitb
    try wp_auto
    ihave Hib := Hibback $$ Hitb
    ihave Hnb : (b ↦{dqb} cvb : IProp GF) $$
        [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnnb
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    rw [list_set_lookup_self _ _ _ (by simpa using Hb.1)]
    ihave HQ := HQb $$ [$Hnb $Hib]
    -- `bytes.Compare` of the two keys
    icases hQ2 a b hPa hPb $$ HQ with ⟨%dq1, %dq2, Hka, Hkb, HQk⟩
    rw [Ha.2, Hb.2]
    wp_apply hC $$ [Hka Hkb] as ⟨Hka, Hkb⟩
    · iframe
    try wp_auto
    ihave HQ := HQk $$ [$Hka $Hkb]
    have Hres : decide (bytes.compareResult (fk a) (fk b) = W64 (-1)) =
        decide (go.GoStringLt (fk a) (fk b)) := by
      unfold bytes.compareResult
      by_cases hlt : go.GoStringLt (fk a) (fk b)
      · simp [hlt]
      · simp only [hlt, ↓reduceIte, decide_false]
        split <;> decide
    rw [Hres]
    iapply HΦ
    iframe
    ipureintro; exact HP
  · -- `Swap`
    iintro !> %l %i %j %a %b %Hij
    iintro !> %Φ ⟨Hs, %HP, HQ⟩ HΦ
    obtain ⟨hi0, hj0, ha, hb⟩ := Hij
    have hp : l.Perm ((l.set (sint.nat i) b).set (sint.nat j) a) :=
      slices.swap_perm l (sint.nat j) (sint.nat i) b a hb ha
    wp_method_call
    wp_call
    wp_auto
    ihave %Hl := ownSlice_len _ _ _ $$ Hs
    have hilt : sint.nat i < l.length := (List.getElem?_eq_some_iff.1 ha).1
    have hjlt : sint.nat j < l.length := (List.getElem?_eq_some_iff.1 hb).1
    have Hbi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := by
      have := Hl.1; refine ⟨hi0, ?_⟩; word
    have Hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := by
      have := Hl.1; refine ⟨hj0, ?_⟩; word
    simp only [Hbi, _root_.and_self, ite_true]
    wp_auto
    simp only [Hbj, _root_.and_self, ite_true]
    wp_auto
    simp only [Hbj, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index s (sint.Z j) l (DFrac.own 1) b hj0 $$ [Hs] as Hs
    · iframe; ipureintro; exact hb
    simp only [Hbi, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index s (sint.Z i) l (DFrac.own 1) a hi0 $$ [Hs] as Hs
    · iframe; ipureintro; exact ha
    wp_apply wp_store_slice_index s (sint.Z i) l b $$ [Hs] as Hs
    · iframe; ipureintro; exact ⟨hi0, by have := Hl.1; word⟩
    try simp only [Hbj, _root_.and_self, ite_true]
    wp_apply wp_store_slice_index s (sint.Z j) _ a $$ [Hs] as Hs
    · iframe; ipureintro; exact ⟨hj0, by simp only [List.length_set]; have := Hl.1; word⟩
    iapply HΦ
    iframe
    ipureintro
    intro c hc
    exact HP c (hp.symm.mem_iff.1 hc)

end proof

end bbolt
end EtcdGrove
end Perennial

/-
The btree's `Ascend` (every item, in order) at the model level of `cache/v3/InvBtree.lean`
(`btree.BTree.Ascend.modelSpec`, derived from the btree's own spec as its siblings are there):
`treeIndex.Compact` and `treeIndex.Keep` visit every key index with it (2026-10-13, the mvcc
store's compaction, unit 5b). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvBtree
public import Spec.k8s_io.utils.third_party.forked.golang.btree.BTree__Ascend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section model
open go_etcd_io.etcd.cache.v3 k8s_io.utils.third_party.forked.golang

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- An iteration from nowhere to nowhere visits every entry. -/
theorem btree.ascRange_none_none {V K : Type} (lt : K → K → Prop) (s : List (V × K)) :
    btree.ascRange lt s none none = s := by
  unfold btree.ascRange
  apply List.filter_eq_self.2
  intro e _
  simp [btree.ascIn]

/-- `t.Ascend(iter)`: Go's documentation: "Ascend calls the iterator for every value in the tree
within the range [first, last], until iterator returns false." The visited items are all the
items, in order, with `iter` meeting `btIterSpec` for an invariant `P` and a final postcondition
`Q`: `Q` if `iter` stopped the iteration, `P` of the number of items if not. A read, on any
fraction. -/
def btree.BTree.Ascend.modelSpec : Prop :=
  ∀ {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] (T : go.GoType)
    [IntoValTyped (GF := GF) T' T] {V : Type}
    (t : Loc) (isItem : T' → V → IProp GF) [∀ p v, Persistent (isItem p v)]
    (less : V → V → Prop) [DecidableRel less] (items : List V) (dq : DFrac)
    (iter : GoFunc) (P : Nat → IProp GF) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree ∗
      ⌜StrictWeakOrder less⌝ ∗ EtcdGrove.ownBTree T t isItem less items dq ∗ P 0 ∗
      btIterSpec iter isItem items P Q }}
    (App (Val (t @!! go.GoType.PointerType (btree.BTree.ty T) @!! go!"Ascend")) (Val #iter))
  {{ RET #(); EtcdGrove.ownBTree T t isItem less items dq ∗ (Q ∨ P items.length) }}

open Classical in
theorem btree.BTree.Ascend.modelSpec_of (wp : btree.BTree.Ascend.spec (GF := GF) (hG := hG)) :
    btree.BTree.Ascend.modelSpec (GF := GF) (hG := hG) := by
  intro T' _ _ T _ V t isItem _ less _ items dq iter P Q
  wp_start_folded as ⟨%Hswo, Ht, HP, #Hit⟩
  unfold EtcdGrove.ownBTree
  icases Ht with ⟨%h, %zs, Ht, %Hzs, #Hall⟩
  subst Hzs
  ihave #Hproto := iterProtocol_of_btIterSpec isItem h zs zs (fun z hz => hz) iter P Q
    _ rfl (btree.ascRange (keyOrder isItem h).lt (zs.map (entry h)) none none)
    (btree.ascRange_none_none _ _) $$ [Hall Hit]
  · iframe #
  iapply wp (keyOrder isItem h) t dq (zs.map (entry h)) iter
    (fun pre b => if b then Q else P pre.length) $$ [Ht HP]
  · iframe # ∗
    simp only [Bool.false_eq_true, ↓reduceIte, List.length_nil]; iexact HP
  inext
  iintro ⟨Ht, Hdone⟩
  iapply HΦ
  isplitl [Ht]
  · iexists h, zs; iframe # ∗; ipureintro; rfl
  · iapply iterDone_model _ P Q _ _ $$ Hdone
    rw [btree.ascRange_none_none]; simp

end model

end EtcdGrove
end Perennial

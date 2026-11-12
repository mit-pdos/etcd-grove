/-
The proof of `Spec/go_etcd_io/bbolt/node__read.lean` (U7, `notes/bbolt-proof-plan.md`; ported from
`old/bbolt/Proof/go_etcd_io/bbolt/node__read.lean`).

The spec takes `pageElemsIn pg` (U7's fix: every element inside the page, which `leafWF`/
`branchWF` give; without it an inode's slice is not the entry's key).
-/
module

public import Spec.go_etcd_io.bbolt.node__read
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.ReadInodeFromPage
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Proof.go_etcd_io.bbolt.Write.ReadPage

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

theorem w16_eq_two_iff (x : w16) : x = W16 2 ↔ x.toNat = 2 := by
  constructor
  · intro h; subst h; rfl
  · intro h; apply BitVec.eq_of_toNat_eq; simpa using h

theorem node.read.wp_proof (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hIL : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hR : internal.common.ReadInodeFromPage.spec (GF := GF) (hG := hG))
    (hK : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG)) :
    node.read.spec (GF := GF) (hG := hG) := by
  intro v n nv p src pg qv Hrd Hfl Hp0 Hpm Hend Hin
  wp_start as ⟨Hn, #Hsrc, Hv⟩
  have Hns : srcLoc (GF := GF) v p src pg ⊢ ⌜src ≠ Src.stale⌝ := by
    cases src with
    | stale => unfold srcLoc; iintro %H; exact H.elim
    | view => iintro _; ipureintro; simp
    | own dq => iintro _; ipureintro; simp
  ihave %hs := Hns $$ Hsrc
  have hlen16 : 0 + 16 ≤ pg.length := by have := Hrd.1; simp only [elemOff] at this; omega
  icases Write.srcLoc_acc qv v p src pg $$ [Hv] with ⟨%dq, Hb, Hback⟩
  · iframe; iexact Hsrc
  icases bytesPointsto_view_read (V := Page) p dq pg 0 p (by simp [loc_add_0]) hlen16 Hp0 $$ Hb
    with ⟨Hh, Hclose⟩
  rw [show (decode ((pg.drop 0).take 16) : Page) = pageHdr pg from rfl]
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  wp_auto
  wp_apply hId $$ [$Hh] as Hh
  try wp_auto
  wp_apply hIL $$ [$Hh] as Hh
  try wp_auto
  ihave Hb := Hclose $$ Hh
  wp_apply hR p pg dq Hrd Hp0 (fun i hi => by have := Hend i hi; omega) $$ [$Hb] as %s ⟨Hb, Hs, Hcap⟩
  try wp_auto
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  have Hlen : (pageInodesAt p pg).length = pageCount pg := by simp [pageInodesAt]
  ihave #Hws := Write.wOwns_pageInodes v p src pg hs Hin Hp0 Hpm $$ Hsrc
  ihave Hv := Hback $$ Hb
  have Hnode : ∀ k : GoSlice, nodeAfterRead nv pg s k =
      { bucket' := nv.bucket', isLeaf' := decide (decode (List.take 2 (List.drop 8 (bytesAt pg 0 16))) = W16 2),
        unbalanced' := nv.unbalanced', spilled' := nv.spilled', key' := k,
        pgid' := decode (List.take 8 (bytesAt pg 0 16)), parent' := nv.parent',
        children' := nv.children', inodes' := s } := by
    intro k
    unfold nodeAfterRead
    congr 1
    exact decide_eq_decide.mpr (w16_eq_two_iff _).symm
  wp_if_destruct
  · have Hc : 0 < pageCount pg := by word
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len
      from ⟨by decide, by word⟩))]
    list_elem (pageInodesAt p pg) (sint.Z (W64 0)).toNat as it
    icases ownSlice_elem_acc (sint.Z (W64 0)) it _ _ _ (by decide) Hit_lookup $$ Hs with ⟨Hit, Hsback⟩
    wp_apply hK $$ [$Hit] as Hit
    try wp_auto
    have Hit0 : it = pageInodeAt p pg 0 := by
      have : (pageInodesAt p pg)[0]? = some (pageInodeAt p pg 0) := by
        simp [pageInodesAt, List.getElem?_map, Hc]
      rw [show (sint.Z (W64 0)).toNat = 0 from rfl, this] at Hit_lookup
      exact (Option.some.inj Hit_lookup).symm
    subst Hit0
    have Hk : (pageInodeAt p pg 0).key' = keySliceAt p pg 0 := by
      unfold pageInodeAt; split <;> rfl
    have Hks : 0 < (if pageFlags pg = leafPageFlag then leafKsize pg 0 else branchKsize pg 0) :=
      (Hrd.2 0 Hc).1
    have Hk32 : (if pageFlags pg = leafPageFlag then leafKsize pg 0 else branchKsize pg 0) < 2 ^ 32 := by
      split
      · unfold leafKsize; exact BitVec.isLt _
      · unfold branchKsize; exact BitVec.isLt _
    have Hklen : sint.Z (keySliceAt p pg 0).len =
        ((if pageFlags pg = leafPageFlag then leafKsize pg 0 else branchKsize pg 0 : Nat) : Int) := by
      unfold keySliceAt bslice
      split <;> (rename_i h; simp only [h, ↓reduceIte] at Hk32 ⊢; exact sint_Z_W64_nat _ (by omega))
    rw [Hk, decide_eq_true (show sint.Z (W64 0) < sint.Z (keySliceAt p pg 0).len by rw [Hklen]; word)]
    wp_apply hA
    try wp_auto
    ihave Hs := Hsback $$ Hit
    rw [list_set_lookup_self _ _ _ Hit_lookup]
    ihave Hn : (n ↦ nodeAfterRead nv pg s (keySliceAt p pg 0) : IProp GF) $$
      [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · rw [Hnode]
      iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    iapply HΦ
    iexists s
    rw [if_pos Hc]
    iframe
    iframe #
  · have Hc : ¬ 0 < pageCount pg := by intro h; apply Hif; word
    try wp_auto
    ihave Hn : (n ↦ nodeAfterRead nv pg s slice.nil : IProp GF) $$
      [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · rw [Hnode]
      iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    iapply HΦ
    iexists s
    rw [if_neg Hc]
    iframe
    iframe #


end proof

end bbolt
end EtcdGrove
end Perennial

module
public import Spec.go_etcd_io.bbolt.node__read
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Spec.go_etcd_io.bbolt.internal.common.ReadInodeFromPage
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Key
public import Spec.go_etcd_io.bbolt.internal.common.Assert

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

theorem node.read.wp_proof (hId : Page.Id.spec (GF := GF) (hG := hG))
    (hIsLeaf : Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (hRead : ReadInodeFromPage.spec (GF := GF) (hG := hG))
    (hK : Inode.Key.spec (GF := GF) (hG := hG))
    (hA : Assert.spec (GF := GF) (hG := hG)) :
    node.read.spec (GF := GF) (hG := hG) := by
  intro nl nv l q pg Hc Hr
  wp_start as ⟨Hn, Hpg⟩
  have H16 := Hr.1
  wp_auto
  icases (page_header_bytes (hG := hG) _ q pg H16 Hc).1 $$ Hpg with ⟨Hhd, Hrest⟩
  wp_apply hId _ (pageOf pg) q $$ [Hhd] as Hhd
  · iframe
  try wp_auto
  wp_apply hIsLeaf _ (pageOf pg) q $$ [Hhd] as Hhd
  · iframe
  try wp_auto
  ihave Hpg := (page_header_bytes (hG := hG) _ q pg H16 Hc).2 $$ [$Hhd $Hrest]
  wp_apply hRead l pg q Hc Hr $$ [Hpg] as %s ⟨Hpg, Hs, Hcap⟩
  · iframe
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  rw [inodesOf_length] at Hsl
  have Hfl : decide (W16 ((pageFlags pg : Nat) : Int) = W16 2) = decide (pageFlags pg = leafPageFlag) := by
    exact decide_eq_decide.mpr (W16_eq_leaf _ (by have := leAt_lt pg 8 2; unfold pageFlags; omega))
  rw [Hfl]
  try simp only
  wp_if_destruct
  · have Hcnt : 0 < pageCount pg := by word
    have Hlk : (inodesOf l pg)[(sint.Z (W64 0)).toNat]? = some (inodeOf l pg 0) := by
      rw [show (sint.Z (W64 0)).toNat = 0 by decide, List.getElem?_eq_getElem (by rw [inodesOf_length]; exact Hcnt)]
      exact congrArg some (inodesOf_get l pg 0 Hcnt)
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len
      from ⟨by decide, by word⟩))]
    icases ownSlice_elem_acc (sint.Z (W64 0)) (inodeOf l pg 0) s _ _ (by decide) Hlk $$ Hs with ⟨Hit, Hsback⟩
    wp_apply hK $$ [$Hit] as Hit
    try wp_auto
    have Hkpos : 0 < sint.Z (inodeOf l pg 0).key'.len := by
      obtain ⟨_, Hleaf, Hbranch⟩ := Hr
      unfold inodeOf
      split
      · have Hk := (Hleaf ‹_›).2 0 Hcnt
        have := leAt_lt pg (elemOff 0 + 8) 4
        simp only; unfold leafKsize at *; word
      · have Hk := ((Hbranch ‹_›).2 0 Hcnt).2.2
        have := leAt_lt pg (elemOff 0 + 4) 4
        simp only; unfold branchKsize at *; word
    rw [decide_eq_true (show sint.Z (W64 0) < sint.Z (inodeOf l pg 0).key'.len by word)]
    wp_apply hA
    try wp_auto
    ihave Hs := Hsback $$ Hit
    rw [list_set_lookup_self _ _ _ Hlk]
    ispecialize HΦ $$ %s
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    iapply HΦ; iframe
  · have Hcnt : pageCount pg = 0 := by word
    try wp_auto
    ispecialize HΦ $$ %s
    rw [ite_eq_left_of_eq_true _ _ (eq_true Hcnt)]
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial

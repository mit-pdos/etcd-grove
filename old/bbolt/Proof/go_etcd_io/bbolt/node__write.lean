module
public import Spec.go_etcd_io.bbolt.node__write
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.Page__Flags
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetFlags
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetCount
public import Spec.go_etcd_io.bbolt.internal.common.WriteInodeToPage
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

theorem node.write.wp_proof (hA : Assert.spec (GF := GF) (hG := hG))
    (hCount : Page.Count.spec (GF := GF) (hG := hG))
    (hFlags : Page.Flags.spec (GF := GF) (hG := hG))
    (hSetFlags : Page.SetFlags.spec (GF := GF) (hG := hG))
    (hSetCount : Page.SetCount.spec (GF := GF) (hG := hG))
    (hW : WriteInodeToPage.spec (GF := GF) (hG := hG)) :
    node.write.spec (GF := GF) (hG := hG) := by
  intro nl nv dqn ins dqs ks vs q p hdr rest Hpc Hc0 Hf0 Hlen Hks Hvs Hkpos Hmax Hfit Hpg
  wp_start as ⟨Hn, Hs, Hd, Hp, Hrest⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_apply hCount $$ [$Hp] as Hp
  try wp_auto
  rw [Hc0]
  try wp_auto
  wp_apply hFlags $$ [$Hp] as Hp
  try wp_auto
  rw [Hf0]
  try wp_auto
  wp_apply hA
  try wp_auto
  unfold internal.common.LeafPageFlag internal.common.BranchPageFlag
  wp_join iprop(p_ptr ↦ p ∗
      p ↦ ({ hdr with flags' := (if nv.isLeaf' then W16 2 else W16 1) } : internal.common.Page))
    at next with [Hp p] as ⟨p, Hp⟩
  · cases hl : nv.isLeaf' <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> wp_auto <;>
      wp_apply hSetFlags $$ [$Hp] as Hp <;> wp_join_done
  wp_if_destruct
  · exfalso; word
  wp_apply hSetCount $$ [$Hp] as Hp
  try wp_auto
  wp_apply hCount $$ [$Hp] as Hp
  try wp_auto
  rw [show sint.Z nv.inodes'.len = (ins.length : Int) by word]
  try simp only
  have Hdec : decide ((if nv.isLeaf' = true then W16 2 else W16 1) = W16 2) = nv.isLeaf' := by
    cases nv.isLeaf' <;> decide
  wp_if_destruct
  · have H0 : ins.length = 0 := by
      have := congrArg BitVec.toNat Hif
      rw [toNat_W16 _ (by omega)] at this
      simpa using this
    have Hins : ins = [] := List.eq_nil_of_length_eq_zero H0
    have Hks0 : ks = [] := List.eq_nil_of_length_eq_zero (by omega)
    have Hvs0 : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst Hins Hks0 Hvs0
    iapply HΦ
    iframe
  · wp_apply hW nv.inodes' ins dqs ks vs q p
      ({ hdr with flags' := (if nv.isLeaf' = true then W16 2 else W16 1), count' := W16 (ins.length : Int) } : internal.common.Page)
      rest Hpc (by omega) Hks Hvs Hkpos Hmax Hfit
      (by
        intro hne
        simp only at hne
        apply Hpg
        cases h : nv.isLeaf'
        · rfl
        · rw [h] at hne; simp at hne) $$ [Hs Hd Hp Hrest] as ⟨Hs, Hd, Hp, Hrest⟩
    · iframe
    try wp_auto
    rw [Hdec]
    iapply HΦ
    iframe

end proof

end bbolt
end EtcdGrove
end Perennial

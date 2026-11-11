/-
`(*Page).FreelistPageIds`'s proof (`internal/common/page.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Page__FreelistPageIds
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeIndex
public import Spec.go_etcd_io.bbolt.internal.common.Page__FreelistPageCount
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsFreelistPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem Page.FreelistPageIds.wp_proof
    (wp_Page_IsFreelistPage : Page.IsFreelistPage.spec (GF := GF) (hG := hG))
    (wp_Page_FreelistPageCount : Page.FreelistPageCount.spec (GF := GF) (hG := hG))
    (wp_UnsafeIndex : UnsafeIndex.spec (GF := GF) (hG := hG)) :
    Page.FreelistPageIds.spec (GF := GF) (hG := hG) := by
  intro l v dq c Hfl Hc H1 H2
  have Hcnt : 0 ≤ sint.Z (if v.count' = W16 65535 then c else W64 (uint.Z v.count')) := by
    split
    · exact Hc ‹_›
    · have := v.count'.isLt; simp only [uint.Z] at *; word
  have Hidx : uint.Z (if v.count' = W16 65535 then W64 1 else W64 0) ≤ 1 := by split <;> decide
  have Hidx0 : 0 ≤ uint.Z (if v.count' = W16 65535 then W64 1 else W64 0) := by simp [uint.Z]
  wp_start as ⟨Hl, Hcell⟩
  wp_auto
  wp_apply wp_Page_IsFreelistPage $$ [$Hl] as Hl
  rw [decide_eq_true Hfl]
  wp_auto
  wp_apply wp_Page_FreelistPageCount l v dq c Hfl Hc H1 (by omega) $$ [$Hl $Hcell] as ⟨Hl, Hcell⟩
  generalize (if v.count' = W16 65535 then W64 1 else W64 0) = idx at *
  generalize (if v.count' = W16 65535 then c else W64 (uint.Z v.count')) = cnt at *
  simp only [pgidSize]
  wp_if_destruct
  · iapply HΦ; iframe
  have Hoff : sint.Z (W64 16 + idx * W64 8) = 16 + 8 * uint.Z idx := by
    have : 0 ≤ uint.Z idx := by simp [uint.Z]
    simp only [uint.Z] at *; word
  wp_apply wp_UnsafeIndex
  · ipureintro; rw [Hoff]; simp only [Loc.add]; omega
  · ipureintro; rw [Hoff]; simp only [Loc.add]; omega
  rw [Hoff]
  wp_func_call
  wp_call
  have h1 : ¬ sint.Z cnt < 0 := by omega
  have h2 : ¬ (l +ₗ (16 + 8 * uint.Z idx) = null) := by
    intro h; have := congrArg Loc.addr h; simp only [Loc.add, null] at this
    have : 0 ≤ uint.Z idx := by simp [uint.Z]
    omega
  have h3 : ¬ (2 ^ 64 < l.addr + (16 + 8 * uint.Z idx) + sint.Z cnt * ((8 : Nat) : Int)) := by
    simp only [maxAddr] at H2 ⊢; omega
  simp only [h1, h2, h3, ite_false]
  wp_auto
  rw [ite_eq_right_of_eq_false _ _ (eq_false Hif)]
  iapply HΦ; iframe

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial

/-
`(*Page).FreelistPageCount`'s proof (`internal/common/page.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Page__FreelistPageCount
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeAdd
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsFreelistPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt
namespace internal
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem Page.FreelistPageCount.wp_proof
    (wp_Page_IsFreelistPage : Page.IsFreelistPage.spec (GF := GF) (hG := hG))
    (wp_UnsafeAdd : UnsafeAdd.spec (GF := GF) (hG := hG)) :
    Page.FreelistPageCount.spec (GF := GF) (hG := hG) := by
  intro l v dq c Hfl Hc H1 H2
  wp_start as ⟨Hl, Hcell⟩
  wp_auto
  wp_apply wp_Page_IsFreelistPage $$ [$Hl] as Hl
  rw [decide_eq_true Hfl]
  wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
  iStructNamed Hl
  wp_auto
  by_cases Ho : v.count' = W16 65535
  · rw [decide_eq_true (show W64 (uint.Z v.count') = W64 65535 by rw [Ho]; rfl)]
    simp only [Ho, ↓reduceIte]
    wp_auto
    wp_apply wp_UnsafeAdd
    · ipureintro; rw [show sint.Z (W64 16) = 16 from rfl]; simp only [Loc.add]; omega
    · ipureintro; rw [show sint.Z (W64 16) = 16 from rfl]; simp only [Loc.add]; omega
    rw [show sint.Z (W64 16) = 16 from rfl]
    wp_auto
    rw [decide_eq_false (by have := Hc Ho; word)]
    wp_auto
    iapply HΦ
    iframe
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef, Ho]
    iframe
  · rw [decide_eq_false (show ¬ W64 (uint.Z v.count') = W64 65535 by
      intro h; apply Ho; apply BitVec.eq_of_toNat_eq; have := congrArg BitVec.toNat h
      simp [uint.Z] at this ⊢; omega)]
    simp only [Ho, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial

/-
`(*Page).BranchPageElements`'s proof (`internal/common/page.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElements
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeAdd

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

theorem Page.BranchPageElements.wp_proof
    (wp_UnsafeAdd : UnsafeAdd.spec (GF := GF) (hG := hG)) :
    Page.BranchPageElements.spec (GF := GF) (hG := hG) := by
  intro p hdr dq H1 H2
  wp_start as Hp
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %hnn⟩
  iStructNamed Hp
  have hc : 0 ≤ uint.Z hdr.count' := by simp [uint.Z]
  have h16 : sint.Z (W64 16) = 16 := rfl
  wp_auto
  wp_if_destruct
  · simp only [show (hdr.count' = W16 0) = True from eq_true Hif, ↓reduceIte]
    iapply HΦ
    iapply typedPointsto_combine _ _ _ hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · wp_apply wp_UnsafeAdd
    · ipureintro; rw [h16]; simp only [Loc.add]; omega
    · ipureintro; rw [h16]; simp only [Loc.add]; omega
    wp_func_call
    wp_call
    have hcl := hdr.count'.isLt
    have hz : sint.Z (W64 (uint.Z hdr.count')) = uint.Z hdr.count' := by
      simp only [uint.Z] at *; word
    have h1 : ¬ sint.Z (W64 (uint.Z hdr.count')) < 0 := by omega
    have h2 : ¬ (p +ₗ sint.Z (W64 16) = null) := by
      rw [h16]; intro h; have := congrArg Loc.addr h; simp only [Loc.add, null] at this; omega
    have h3 : ¬ (2 ^ 64 < p.addr + sint.Z (W64 16) + sint.Z (W64 (uint.Z hdr.count')) *
        ((16 : Nat) : Int)) := by
      rw [hz, h16]; simp only [maxAddr] at H2; omega
    simp only [h1, h2, h3, ite_false]
    wp_auto
    simp only [show (hdr.count' = W16 0) = False from eq_false Hif, ↓reduceIte]
    rw [h16]
    iapply HΦ
    iapply typedPointsto_combine _ _ _ hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial

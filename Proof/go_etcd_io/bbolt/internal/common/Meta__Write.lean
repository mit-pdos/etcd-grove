/-
`(*Meta).Write`'s proof (`internal/common/meta.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Meta__Write
public import Spec.go_etcd_io.bbolt.internal.common.Page__SetFlags
public import Spec.go_etcd_io.bbolt.internal.common.Page__Meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Copy
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Sum64

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

theorem Meta.Write.wp_proof
    (wp_Meta_Sum64 : Meta.Sum64.spec (GF := GF) (hG := hG))
    (wp_Meta_Copy : Meta.Copy.spec (GF := GF) (hG := hG))
    (wp_Page_Meta : Page.Meta.spec (GF := GF) (hG := hG))
    (wp_Page_SetFlags : Page.SetFlags.spec (GF := GF) (hG := hG)) :
    Meta.Write.spec (GF := GF) (hG := hG) := by
  intro l p v hdr w Hroot Hfree Hl0 Hp0 Hp16
  wp_start as ⟨Hl, Hp, Hw⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hlnn⟩
  iStructNamed Hl
  icases typedPointsto_not_null_dup _ _ _ $$ root with ⟨root, %Hrnn⟩
  iStructNamedPrefix root "r_"
  icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hpnn⟩
  iStructNamedPrefix Hp "p_"
  wp_auto
  rw [decide_eq_false (by omega)]
  wp_auto
  wp_if_destruct
  have Hge := Hif
  wp_if_destruct
  rotate_left
  · exfalso; rcases Hfree with h | h
    · omega
    · apply Hif; apply BitVec.eq_of_toNat_eq; simp only [h, pgidNoFreelist]; rfl
  all_goals
    ihave Hp : p ↦ ({ hdr with id' := v.txid' % W64 2 } : Page) $$ [p_id p_flags p_count p_overflow]
    · iapply typedPointsto_combine _ _ _ Hpnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    wp_apply wp_Page_SetFlags $$ [$Hp] as Hp
    ihave Hr : l.[Meta, go!"root"] ↦ v.root' $$ [r_root r_sequence]
    · iapply typedPointsto_combine _ _ _ Hrnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hl : l ↦ v $$ [magic version pageSize flags Hr freelist pgid txid checksum]
    · iapply typedPointsto_combine _ _ _ Hlnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    wp_apply wp_Meta_Sum64 l v (DFrac.own 1) Hl0 $$ [$Hl] as Hl
    iStructNamed Hl
    ihave Hl : l ↦ ({ v with checksum' := metaSum v } : Meta) $$ [magic version pageSize flags root freelist pgid txid checksum]
    · iapply typedPointsto_combine _ _ _ Hlnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    wp_apply wp_Page_Meta p Hp0 Hp16
    wp_apply wp_Meta_Copy $$ [$Hl $Hw] as ⟨Hl, Hw⟩
    iapply HΦ
    iframe

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial

/-
`(*Meta).Validate`'s proof (`internal/common/meta.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Meta__Validate
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

theorem Meta.Validate.wp_proof
    (wp_Meta_Sum64 : Meta.Sum64.spec (GF := GF) (hG := hG)) :
    Meta.Validate.spec (GF := GF) (hG := hG) := by
  intro l v dq Hl0
  wp_start as Hl
  ihave #Hep : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors $$ []
  · iPkgInit
  ihave #Hei : (go_etcd_io.bbolt.errors.bboltErrorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hep
  unfold go_etcd_io.bbolt.errors.bboltErrorsInit go_etcd_io.bbolt.errors.bboltErrorsVars
    go_etcd_io.bbolt.errors.bboltErrVar
  icases Hei with ⟨%_, #-, %_, -, ⟨%eI, #HI, %_, #-⟩, -, ⟨%eV, #HV, %_, #-⟩, ⟨%eC, #HC, %_, #-⟩, -⟩
  have HIn : GoInterface.ok eI ≠ GoInterface.nil := nofun
  have HVn : GoInterface.ok eV ≠ GoInterface.nil := nofun
  have HCn : GoInterface.ok eC ≠ GoInterface.nil := nofun
  icases typedPointsto_not_null_dup _ _ _ $$ Hl with ⟨Hl, %Hnn⟩
  iStructNamed Hl
  wp_auto
  have hM : v.magic'.toNat = boltMagic ↔ v.magic' = W32 3977042669 := by
    unfold boltMagic; constructor <;> intro h
    · apply BitVec.eq_of_toNat_eq; rw [h]; rfl
    · rw [h]; rfl
  have hV : v.version'.toNat = boltVersion ↔ v.version' = W32 2 := by
    unfold boltVersion; constructor <;> intro h
    · apply BitVec.eq_of_toNat_eq; rw [h]; rfl
    · rw [h]; rfl
  by_cases hm : v.magic' = W32 3977042669
  · rw [decide_eq_true hm]
    wp_auto
    by_cases hv : v.version' = W32 2
    · rw [decide_eq_true hv]
      wp_auto
      ihave Hl : l ↦{dq} v $$ [magic version pageSize flags root freelist pgid txid checksum]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      wp_apply wp_Meta_Sum64 l v dq Hl0 $$ [$Hl] as Hl
      by_cases hc : v.checksum' = metaSum v
      · rw [decide_eq_true hc]
        wp_auto
        iapply HΦ
        iframe
        ipureintro
        exact ⟨fun _ => ⟨hM.2 hm, hV.2 hv, hc⟩, fun _ => rfl⟩
      · rw [decide_eq_false hc]
        wp_auto
        iapply HΦ
        iframe
        ipureintro
        exact ⟨fun h => absurd h HCn, fun h => absurd h.2.2 hc⟩
    · rw [decide_eq_false hv]
      wp_auto
      iapply HΦ
      isplitr []
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ipureintro
      exact ⟨fun h => absurd h HVn, fun h => absurd (hV.1 h.2.1) hv⟩
  · rw [decide_eq_false hm]
    wp_auto
    iapply HΦ
    isplitr []
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ipureintro
    exact ⟨fun h => absurd h HIn, fun h => absurd (hM.1 h.1) hm⟩

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial

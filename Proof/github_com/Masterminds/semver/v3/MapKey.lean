/-
`semver.Version` as a map key: Go's `==` on it is equality of values (its six fields, three `uint64`s
and three strings, are compared in turn), so every version is a safe map key (`SafeMapKey`). For
`storage/schema`'s `schemaChanges` (a `map[semver.Version][]schemaChange` literal; prove-initleft,
2026-11-21).
-/
module

public import Spec.github_com.Masterminds.semver.v3.New

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

deriving instance DecidableEq for github_com.Masterminds.semver.v3.Version

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section inj
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [package_sem : github_com.Masterminds.semver.v3.Assumptions]

/-- A field read is deterministic, so equal struct values have equal fields. -/
private theorem semver.field_eq {S T : Type} (op : GoInstruction)
    (proj : S → T) (hg : ∀ z : S, is_go_step_pure op #z = Eq (Val #(proj z))) {x y : S}
    (h : (#x : val) = #y) : (#(proj x) : val) = #(proj y) := by
  have e := hg x
  rw [h, hg y] at e
  have h2 : (Val #(proj y) : Expr) = Val #(proj x) := (congrFun e (Val #(proj x))).mpr rfl
  injection h2.symm

/-- A `semver.Version` value determines its fields: `schemaChanges`' keys (`map[semver.Version]...`)
are compared by value. -/
instance semver.Version.intoValInj [go.BasicIntoValInj] :
    go.IntoValInj github_com.Masterminds.semver.v3.Version where
  intoVal_inj x y h := by
    have h1 := go.intoVal_inj (semver.field_eq _ _ (fun z =>
      (github_com.Masterminds.semver.v3.Version.TypeAssumptions.get'major z).isGoStep_det_internal.isGoStep_pure_det) h)
    have h2 := go.intoVal_inj (semver.field_eq _ _ (fun z =>
      (github_com.Masterminds.semver.v3.Version.TypeAssumptions.get'minor z).isGoStep_det_internal.isGoStep_pure_det) h)
    have h3 := go.intoVal_inj (semver.field_eq _ _ (fun z =>
      (github_com.Masterminds.semver.v3.Version.TypeAssumptions.get'patch z).isGoStep_det_internal.isGoStep_pure_det) h)
    have h4 := go.intoVal_inj (semver.field_eq _ _ (fun z =>
      (github_com.Masterminds.semver.v3.Version.TypeAssumptions.get'pre z).isGoStep_det_internal.isGoStep_pure_det) h)
    have h5 := go.intoVal_inj (semver.field_eq _ _ (fun z =>
      (github_com.Masterminds.semver.v3.Version.TypeAssumptions.get'metadata z).isGoStep_det_internal.isGoStep_pure_det) h)
    have h6 := go.intoVal_inj (semver.field_eq _ _ (fun z =>
      (github_com.Masterminds.semver.v3.Version.TypeAssumptions.get'original z).isGoStep_det_internal.isGoStep_pure_det) h)
    cases x; cases y
    simp only at h1 h2 h3 h4 h5 h6
    subst h1 h2 h3 h4 h5 h6; rfl

end inj

/-- Step Go's `==` on two versions, the field `h` says differ deciding it. -/
local macro "semver_eq_tac" h:ident H:ident : tactic =>
  `(tactic| (wp_auto; iterate 8 (try simp only [$h:ident, _root_.decide_true, _root_.decide_false]; try wp_auto)
             iexact $H:ident))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.Masterminds.semver.v3.Assumptions]

instance semver.Version.safeMapKey (k : github_com.Masterminds.semver.v3.Version) :
    SafeMapKey (GF := GF) github_com.Masterminds.semver.v3.Version.ty k where
  key_ok := trivial
  wp_go_eq_map_key k' _ s E Φ := by
    by_cases hk : k = k'
    · subst hk
      simp only [_root_.decide_true]
      iintro HΦ
      wp_auto
      iexact HΦ
    · simp only [hk, decide_false]
      rcases k with ⟨a, b, c, d, e, f⟩
      rcases k' with ⟨a', b', c', d', e', f'⟩
      simp only [github_com.Masterminds.semver.v3.Version.mk.injEq, not_and] at hk
      iintro HΦ
      by_cases h1 : a = a'
      · subst h1
        by_cases h2 : b = b'
        · subst h2
          by_cases h3 : c = c'
          · subst h3
            by_cases h4 : d = d'
            · subst h4
              by_cases h5 : e = e'
              · subst h5
                have h6 : f ≠ f' := hk rfl rfl rfl rfl rfl
                semver_eq_tac h6 HΦ
              · semver_eq_tac h5 HΦ
            · semver_eq_tac h4 HΦ
          · semver_eq_tac h3 HΦ
        · semver_eq_tac h2 HΦ
      · semver_eq_tac h1 HΦ

end proof

end EtcdGrove
end Perennial

/-
Proof of `Spec/github_com/Masterminds/semver/v3/MustParse.lean`, over `NewVersion`'s spec (a
trust-boundary axiom until 2026-11-22, prove-ps2-client).
-/
module

public import Spec.github_com.Masterminds.semver.v3.MustParse
public import Spec.github_com.Masterminds.semver.v3.NewVersion

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.Masterminds.semver.v3.Assumptions]

/-- `MustParse(s)`: `NewVersion(s)`, a panic on its error. -/
theorem semver.MustParse.wp_proof
    (wp_NewVersion : semver.NewVersion.spec (GF := GF) (hG := hG)) :
    semver.MustParse.spec (GF := GF) (hG := hG) := by
  intro s
  wp_start as #Hpi
  wp_auto
  wp_apply wp_NewVersion s as %v %err Hr
  icases Hr with (⟨%Hok, %x, #Hx, #His⟩ | %Hbad)
  · obtain ⟨Hv, Hnn, Herr⟩ := Hok
    subst Herr
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; exact Hv
    iexists v, x
    iframe Hx His
    ipureintro; exact ⟨rfl, Hnn⟩
  · obtain ⟨Hv, Herr⟩ := Hbad
    cases err with
    | nil => exact absurd rfl Herr
    | ok i =>
    simp only
    wp_auto
    wp_apply wp_panic
    iapply HΦ
    iright
    ipureintro
    exact ⟨Hv, _, rfl⟩

end proof

end EtcdGrove
end Perennial

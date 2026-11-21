/-
**`semver.MustParse`'s pure outcome** (2026-10-24, the merge of the rafthttp work into `lean`):
since D22 (2026-10-23) its spec also gives the version's `semverIs`; the stream reader's and the
handlers' proofs need only whether it parsed (`MustParse.pure`), and the version's read-only
points-to (`MustParse.ver`, 2026-11-20: `Version`'s methods read it). Lean-first.
-/
module

public import Spec.github_com.Masterminds.semver.v3.MustParse

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

/-- `semver.MustParse(s)`: a version, not nil, if `s` parses, else a panic. -/
theorem semver.MustParse.pure (hMP : semver.MustParse.spec (GF := GF) (hG := hG)) (s : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
      (App (Val (@! github_com.Masterminds.semver.v3.MustParse)) (Val #s))
    {{ (r : val), RET r;
        ⌜(apply.semverValid s ∧ ∃ v : Loc, r = #v ∧ v ≠ null) ∨
          (¬ apply.semverValid s ∧ ∃ p : val, r = PanicV p)⌝ }} := by
  iintro %Φ #Hp HΦ
  wp_apply hMP s as %r Hr
  icases Hr with (⟨%Hv, %v, %x, %Hrv, -, -⟩ | %Hn)
  · iapply HΦ; ipureintro; exact Or.inl ⟨Hv, v, Hrv⟩
  · iapply HΦ; ipureintro; exact Or.inr Hn

/-- `semver.MustParse(s)`: a version, not nil, read-only, if `s` parses, else a panic. -/
theorem semver.MustParse.ver (hMP : semver.MustParse.spec (GF := GF) (hG := hG)) (s : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
      (App (Val (@! github_com.Masterminds.semver.v3.MustParse)) (Val #s))
    {{ (r : val), RET r;
        (∃ (v : Loc) (x : github_com.Masterminds.semver.v3.Version),
          ⌜apply.semverValid s ∧ r = #v ∧ v ≠ null⌝ ∗ v ↦□ x) ∨
        ⌜¬ apply.semverValid s ∧ ∃ p : val, r = PanicV p⌝ }} := by
  iintro %Φ #Hp HΦ
  wp_apply hMP s as %r Hr
  icases Hr with (⟨%Hv, %v, %x, %Hrv, #Hx, -⟩ | %Hn)
  · iapply HΦ; ileft; iexists v, x; iframe Hx; ipureintro; exact ⟨Hv, Hrv⟩
  · iapply HΦ; iright; ipureintro; exact Hn

/-- `semver.MustParse(s)` of a string that parses: a version, not nil, read-only. -/
theorem semver.MustParse.valid (hMP : semver.MustParse.spec (GF := GF) (hG := hG)) (s : GoString)
    (hs : apply.semverValid s) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
      (App (Val (@! github_com.Masterminds.semver.v3.MustParse)) (Val #s))
    {{ (v : Loc) (x : github_com.Masterminds.semver.v3.Version), RET #v; ⌜v ≠ null⌝ ∗ v ↦□ x }} := by
  iintro %Φ #Hp HΦ
  wp_apply hMP s as %r Hr
  icases Hr with (⟨%Hv, %v, %x, %Hrv, #Hx, -⟩ | %Hn)
  · obtain ⟨rfl, hnn⟩ := Hrv
    iapply HΦ; iframe Hx; ipureintro; exact hnn
  · exact absurd hs Hn.1

end proof

end EtcdGrove
end Perennial

/-
**`semver.MustParse`'s pure outcome** (2026-10-24, the merge of the rafthttp work into `lean`):
since D22 (2026-10-23) its spec also gives the version's `semverIs`; the stream reader's and the
handlers' proofs need only whether it parsed. Lean-first.
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

/-- `semver.MustParse(s)`: a version, not nil, if `s` parses, else a panic. -/
theorem semver.MustParse.pure (hMP : semver.MustParse.spec (GF := GF) (hG := hG)) (s : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
      (App (Val (@! github_com.Masterminds.semver.v3.MustParse)) (Val #s))
    {{ (r : val), RET r;
        ⌜(apply.semverValid s ∧ ∃ v : Loc, r = #v ∧ v ≠ null) ∨
          (¬ apply.semverValid s ∧ ∃ p : val, r = PanicV p)⌝ }} := by
  iintro %Φ #Hp HΦ
  wp_apply hMP s as %r Hr
  icases Hr with (⟨%Hv, %v, %Hrv, -⟩ | %Hn)
  · iapply HΦ; ipureintro; exact Or.inl ⟨Hv, v, Hrv⟩
  · iapply HΦ; ipureintro; exact Or.inr Hn

end proof

end EtcdGrove
end Perennial

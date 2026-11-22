/-
`semver.NewVersion`: the trust boundary (`github.com/Masterminds/semver/v3`'s parser, a regular
expression, is untranslated). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.RestModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.Masterminds.semver.v3.Assumptions]

/-- `semver.NewVersion(s)`: if `s` parses (`semverValid`), a fresh version, not nil, read-only
(nothing else holds it), the version of `s` (`apply.semverIs`), and a nil error; else a non-nil
error (`ErrVersionTooLong`, `ErrInvalidSemVer`, or a `fmt.Errorf` of a bad number). Since
2026-11-22 (prove-ps2-client) the trust boundary in place of `MustParse` (its body: `NewVersion`,
then `panic(err)` on an error) and `version.Cluster`. -/
abbrev semver.NewVersion.spec : Prop :=
  ∀ (s : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 }}
    (App (Val (@! github_com.Masterminds.semver.v3.NewVersion)) (Val #s))
  {{ (v : Loc) (err : GoInterface), RET (PairV #v #err);
      (⌜apply.semverValid s ∧ v ≠ null ∧ err = GoInterface.nil⌝ ∗
        ∃ x : github_com.Masterminds.semver.v3.Version, v ↦□ x ∗ apply.semverIs v s) ∨
      ⌜¬ apply.semverValid s ∧ err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial

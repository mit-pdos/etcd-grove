/-
The trust boundary: `semver.NewVersion` (`github.com/Masterminds/semver/v3`'s parser, a regular
expression over `regexp`, is untranslated). Since 2026-11-22 (prove-ps2-client) in place of the
axioms of `MustParse` and `version.Cluster`, both proved over it.
-/
module

public import Spec.github_com.Masterminds.semver.v3.NewVersion

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.Masterminds.semver.v3.Assumptions]

/-- **Trust boundary**: `NewVersion(s)` (semver v3.5.0's `version.go`) returns `nil` and
`ErrVersionTooLong` past `MaxVersionLen`; else (`CoerceNewVersion`, true by default) the result of
`coerceNewVersion`, or of `StrictNewVersion`: on a match of its regular expression a fresh
`&Version{...}` and `nil`, else `nil` and a non-nil error (`ErrInvalidSemVer`, or a
`fmt.Errorf` of a number that does not parse); it does not panic. That `s` parses is what
`apply.semverValid s` names, and the version is `s`'s (`apply.semverIs`). -/
axiom semver.NewVersion.wp_proof : semver.NewVersion.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

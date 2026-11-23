/-
The trust boundary: `semver.Version.LessThan` (translated with its body, `version.go:486-488`:
`v.Compare(o) < 0`; `Compare`'s proof is `Version__Compare.lean`). 2026-11-23, prove-ps2-version:
proved 2026-11-22 over receivers' points-tos, reverted to this axiom (the spec's file says why).
-/
module

public import Spec.github_com.Masterminds.semver.v3.Version__LessThan

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

axiom semver.Version.LessThan.wp_proof : semver.Version.LessThan.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

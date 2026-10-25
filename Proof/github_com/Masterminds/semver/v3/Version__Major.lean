/-
The trust boundary: `semver.Version.Major` (`github.com/Masterminds/semver/v3` is names-only).
-/
module

public import Spec.github_com.Masterminds.semver.v3.Version__Major

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (rafthttp stage 5e-3): Masterminds' `Major` (`version.go`) allocates
or reads a version's fields, without panicking. -/
axiom semver.Version.Major.wp_proof : semver.Version.Major.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

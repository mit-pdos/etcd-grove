/-
The trust boundary: `semver.Version.Minor` (`github.com/Masterminds/semver/v3` is names-only).
-/
module

public import Spec.github_com.Masterminds.semver.v3.Version__Minor

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

/-- **Trust boundary** (rafthttp stage 5e-3): Masterminds' `Minor` (`version.go`) allocates
or reads a version's fields, without panicking. -/
axiom semver.Version.Minor.wp_proof : semver.Version.Minor.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

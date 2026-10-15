/-
The trust boundary: `semver.MustParse` (`github.com/Masterminds/semver/v3` is names-only).
-/
module

public import Spec.github_com.Masterminds.semver.v3.MustParse

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

axiom semver.MustParse.wp_proof : semver.MustParse.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

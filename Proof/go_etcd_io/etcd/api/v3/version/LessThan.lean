/-
The trust boundary: `version.LessThan` (`api/v3/version`, names only: it compares
`semver.Version`s with their `LessThan`, of `github.com/Masterminds/semver`, names only).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.version.LessThan

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
variable [package_sem : go_etcd_io.etcd.api.v3.version.Assumptions]

axiom version.LessThan.wp_proof : version.LessThan.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

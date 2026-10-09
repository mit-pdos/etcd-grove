/-
The trust boundary: `go_humanize.Bytes` (`github.com/dustin/go-humanize` is names-only).
-/
module

public import Spec.github_com.dustin.go_humanize.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3 go_etcd_io.etcd.pkg.v3 go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

axiom go_humanize.Bytes.wp_proof : go_humanize.Bytes.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

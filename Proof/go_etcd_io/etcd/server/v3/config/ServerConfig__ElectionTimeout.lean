/-
The trust boundary: `config.ServerConfig.ElectionTimeout` (`server/v3/config` is names-only: `ElectionTimeout` computes a duration from two fields).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__ElectionTimeout

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

axiom config.ServerConfig.ElectionTimeout.wp_proof : config.ServerConfig.ElectionTimeout.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

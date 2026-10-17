/-
The trust boundary: `convertToClusterVersion` (`cluster_util.go`, names-only: its body calls
semver's `NewVersion` and `New`, names-only too). pr-verify etcd#22589.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.convertToClusterVersion

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

axiom convertToClusterVersion.wp_proof : convertToClusterVersion.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

/-
The trust boundary: `clientv3.streamKeyFromCtx(ctx)` (`client/v3/watch.go`; the watch slice's unit
W-C) returns some string. Its body calls grpc's `metadata.FromOutgoingContext` (the package
`google.golang.org/grpc/metadata` is translated names-only) and `fmt.Sprintf("%+v", ...)` of a map
(Perennial does not model `fmt`'s formatting of a map), so it is assumed.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.streamKeyFromCtx

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

axiom streamKeyFromCtx.wp_proof : streamKeyFromCtx.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

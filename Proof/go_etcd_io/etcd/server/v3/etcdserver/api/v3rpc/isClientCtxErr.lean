/-
The trust boundary: `v3rpc.isClientCtxErr` (`util.go`, names only: it classifies an error for the
logs, through grpc's `status.FromError` and the status's code and message, names only).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.isClientCtxErr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

axiom v3rpc.isClientCtxErr.wp_proof : v3rpc.isClientCtxErr.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

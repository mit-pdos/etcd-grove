/-
`v3rpc.LeaseServer.LeaseRevoke` (`v3rpc/lease.go`; the client lease's stage (c)). Lean-first (no
Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvLease.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLease

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`ls.LeaseRevoke(ctx, r)`** on the `*LeaseServer` `ls` over the server `s`
(`leaseServerAt`), whose lease methods meet the contract `raftLessor s E S`, in a gRPC run (its
context, the resource `S`), on a decoded request: `ls.le.LeaseRevoke(ctx, r)`, then the header
filled: `S` back, and the server's response with its header filled by the cluster `cid` and the
member `mid`, its revision not `0` and reached (and nothing else), or `nil` and a non-nil error
(`leaseGrantOut`, `leaseRevokeOut`). -/
abbrev v3rpc.LeaseServer.LeaseRevoke.spec : Prop :=
  ∀ (p s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64) (E : apply.AEnv GF) (S : IProp GF)
    (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (m : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.leaseServerAt p s A cid mid ∗ v3rpc.raftLessor s E S ∗ S ∗
      context.isContext ci cd ∗ grpcRunCtx ci ∗ v3rpc.leaseRevokeReqIs r m }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.LeaseServer.ty @!! go!"LeaseRevoke"))
      (Val #(GoInterface.ok ci))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ v3rpc.leaseRevokeOut E cid mid resp err }}

end spec

end EtcdGrove
end Perennial

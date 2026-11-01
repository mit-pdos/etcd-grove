/-
`v3rpc.LeaseServer.LeaseLeases` (`v3rpc/lease.go`; the lease rows at the gRPC level,
`notes/lease-grpc-plan.md`). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/InvLeaseRead.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvLeaseRead

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`ls.LeaseLeases(ctx, r)`** on the `*LeaseServer` `ls` over the server `s`
(`leaseServerAt`), whose lease reads meet the contract `raftLeaseRead s E γl S A.revR`, with the
contract's per-call resources `S` and the header's revision reader `A.revR` (which the server's
`newHeader()` reads too), at a context and the lower bounds `n`, `m`: `s.LeaseLeases(ctx, r)`,
`ErrLeaseNotFound` turned into an empty listing, another error through `togRPCError`, then the
header filled. Everything back, and `leaseLeasesOut`: on success the response with its header
filled and the server's listing with each lease's verdict (or the empty listing); on an error
`nil`. -/
abbrev v3rpc.LeaseServer.LeaseLeases.spec : Prop :=
  ∀ (p s : Loc) (A : v3rpc.KVAns GF) (cid mid : w64) (E : apply.AEnv GF) (γl : GName)
    (S : IProp GF) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (n m : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.leaseServerAt p s A cid mid ∗ v3rpc.raftLeaseRead s E γl S A.revR ∗ S ∗ A.revR ∗
      context.isContext ci cd ∗ auth.authPubLbM E.authMode n ∗ lease.lessorLb γl m }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.LeaseServer.ty @!! go!"LeaseLeases"))
      (Val #(GoInterface.ok ci))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); S ∗ A.revR ∗
      v3rpc.leaseLeasesOut s E γl ci n m cid mid resp err }}

end spec

end EtcdGrove
end Perennial

/-
`cs.MemberList(ctx, r)` (`member.go`): the Cluster service's member list, over the server's `MemberList`. Lean-first (no Rocq counterpart); auth-mediation M2 (2026-11-20), vocabulary
`v3rpc/InvCluster.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvCluster
public import Proof.context.LibKeys
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Members

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

/-- **`cs.MemberList(ctx, r)`**: the server's `MemberList(ctx, r)` (with `r.Linearizable` the read
index, then the authenticated-user guard, then the cluster's members; its resources as
`EtcdServer.MemberList.spec`'s), then `togRPCError` on an error, or the response of the header and
the members. An error grpc's server takes (`srvErrOk`); on `nil` the guard's token `authedRes` for
some auth info and, with `r.Linearizable`, the read index (`readIndexOk`, `readServed`); on an error
(and no response), made by `togRPCError` of the server's `e0`, an `e0` that is one of the auth
package's variables refused for the authenticated class's reason (`authedWhy` relative to the
caller's lower bound `n` of the auth store's published index). -/
abbrev v3rpc.ClusterServer.MemberList.spec : Prop :=
  ∀ (p s cl : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (tok : Option GoString) (r : Loc) (lin : Bool)
    (dq : DFrac) (c : w64) (g : GName) (Q : List EntryModel → IProp GF) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.clusterServerIs p s cl ∗ v3rpc.clusterHdrOk s cl ∗
      isServerReq s E ρ ∗ isServerRead s E γr ∗ □ auth.authPubLbM E.authMode n ∗
      mvcc.txnCtx ctx cd ∗ context.libCtxOk ctx ∗
      □ (⌜E.authMode.isOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗ E.RD ∗
      structFieldRef etcdserverpb.MemberListRequest go!"Linearizable" r ↦{dq} lin ∗
      srvReadReader s γr ∗ committedAtLeast γr c ∗ savedPredOwn g DFrac.discard Q ∗
      kvDep γr.kv Q }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.ClusterServer.ty @!! go!"MemberList"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); E.RD ∗
      structFieldRef etcdserverpb.MemberListRequest go!"Linearizable" r ↦{dq} lin ∗
      srvReadReader s γr ∗ go_etcd_io.etcd.cache.v3.srvErrOk err ∗
      (∀ _ : err ≠ GoInterface.nil, ⌜resp = null⌝ ∗ ∃ e0 : GoInterface, ⌜e0 ≠ GoInterface.nil⌝ ∗
        v3rpc.grpcErrOut (fun _ => True) e0 err ∗
        (authErrVarIs e0 -∗ authedWhy E.authMode n tok e0)) ∗
      (∀ _ : err = GoInterface.nil,
        (∃ ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo, authedRes E.authMode ai) ∗
        (∀ _ : lin = true, readIndexOk γr c ∗ readServed γr c g)) }}

end spec

end EtcdGrove
end Perennial

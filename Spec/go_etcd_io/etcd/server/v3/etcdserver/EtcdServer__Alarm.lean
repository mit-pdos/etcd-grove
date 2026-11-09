/-
## `(*EtcdServer).Alarm(ctx, r)`

**Users.** The gRPC maintenance handler (`api/v3rpc/maintenance.go:259`, `GET` and `DEACTIVATE`
from clients: W0's `alarmList`, `alarmDisarm` and, since W0's round 5, `alarmActivate` (`.req
(.alarmActivate al)`; the message is 3h's `.alarmActivate al` either way: `ao` says whose), with the
client's update), the quota's alarmer
(`api/v3rpc/quota.go:48`, `ACTIVATE` of `NOSPACE`, no update: the entry's commit is an environment
step the cluster's invariant takes by the `envUpd` the server holds, `EnvStep.alarm`; 2a's need,
`req/go_etcd_io_etcd_server_v3_etcdserver.md`, "from 2a", item 5). Snippet: none of its own (the
quota path is 2a's). Untranslated (names only): an assumed contract until its body is translated
(it is `raftRequest` and a type assertion).

**Proof sketch.** `raftRequest(ctx, {Alarm: r})` at `ir` (3h's `alarmReqOwn` unwrapped and wrapped
into `irrOwn`; `raftRequest.spec` with the same `ao`), then `resp.(*pb.AlarmResponse)` (`respTy`;
an activation's `irrReply` is an `*AlarmResponse` too: 3a's alarm applier answers one).

**Changes.** New (no old spec).

**Margin.** An activation's reply is not stated (its caller ignores it).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **An alarm request** (`ir`, 3h's model of the message: `.req .alarmList` (`GET`), `.req
(.alarmDisarm al)` (`DEACTIVATE`), `.alarmActivate al` (`ACTIVATE`)), through raft; the caller's
update over `ao` (`irrAsks`: a client's, for any of them; none for the quota's activation). -/
def EtcdServer.Alarm.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (q : Qp) (ctx : GoInterface) (p tls : Principal) (lo : Nat) (r : Loc) (dq : DFrac)
    (ir : IrrBody) (ao : Option Req) (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvGate s q ∗
      Context.ctxOk ctx ∗ reqCtxOk ctx ∗ reqPrin ctx p tls ∗ threadTok ∗ alarmReqOwn r dq ir ∗ authLb γ lo ∗
      ⌜irrAsks ir ao⌝ ∗ irrUpd γ p tls lo ao false Q }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Alarm")) (Val #ctx)) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvGate s q ∗ threadTok ∗ alarmReqOwn r dq ir ∗
      ((∃ σ σ' res, irrFired ao Q σ σ' res ∗
          match ao with
          | some aq => srvReply (reqReply γ aq) res resp err
          | none => iprop(⌜err = GoInterface.nil⌝ ∨ ∃ e, ⌜resp = null ∧ srvErrOf err e⌝ ∗ srvErrShape err)) ∨
       (⌜resp = null ∧ srvUnfired err⌝ ∗ srvErrShape err ∗ irrUpd γ p tls lo ao false Q) ∨
       (⌜resp = null ∧ srvIndef err⌝ ∗ srvErrShape err)) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial

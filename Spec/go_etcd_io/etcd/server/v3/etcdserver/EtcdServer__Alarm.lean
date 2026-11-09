/-
## `(*EtcdServer).Alarm(ctx, r)`

**Users.** The gRPC maintenance handler (`api/v3rpc/maintenance.go:259`, `GET` and `DEACTIVATE`
from clients: W0's `alarmList`, `alarmDisarm` and, since W0's round 5, `alarmActivate` (`.req
(.alarmActivate al)`), with the client's update), the quota's alarmer
(`api/v3rpc/quota.go:48`, `ACTIVATE` of `NOSPACE`, no update: the entry's commit is an environment
step the cluster's invariant takes by the `envUpd` the server holds, `EnvStep.alarm`; 2a's need,
`req/go_etcd_io_etcd_server_v3_etcdserver.md`, "from 2a", item 5). Snippet: none of its own (the
quota path is 2a's). Untranslated (names only): an assumed contract until its body is translated
(it is `raftRequest` and a type assertion).

**Proof sketch.** `raftRequest(ctx, {Alarm: r})` at `ir` (`raftRequest.spec`: the update only for
`.req`, `IrrBody.fires`), then `resp.(*pb.AlarmResponse)` (`respTy`; for an activation `irrReply`
says nothing: 3a's alarm applier answers an `*AlarmResponse`, requested in `req/`).

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

/-- **An alarm request** (`ir`: a client's `.req .alarmList`, `.req (.alarmDisarm al)`, `.req
(.alarmActivate al)`, with the caller's update; or the quota's `.alarmActivate al`, with none),
through raft. -/
def EtcdServer.Alarm.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (p tls : Principal) (lo : Nat) (r : Loc) (dq : DFrac)
    (ir : IrrBody) (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗
      Context.ctxOk ctx ∗ reqCtxOk ctx ∗ reqPrin ctx p tls ∗ threadTok ∗ alarmReqOwn r dq ir ∗ authLb γ lo ∗
      (if ir.fires then
        AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
          <{ ∀∀ (σ' : State) (res : Resp), ⌜irrStep p tls lo ir σ σ' res⌝ ∗ etcdState γ σ',
             COMM Q σ σ' res }>
      else True) }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Alarm")) (Val #ctx)) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); threadTok ∗ alarmReqOwn r dq ir ∗
      ((∃ σ σ' res, (if ir.fires then Q σ σ' res else True) ∗
          match ir with
          | .req rq => srvReply (reqReply γ rq) res resp err
          | _ => iprop(⌜err = GoInterface.nil⌝ ∨ ∃ e, ⌜resp = null ∧ srvErrOf err e⌝ ∗ srvErrShape err)) ∨
       (⌜resp = null ∧ srvUnfired err⌝ ∗ srvErrShape err ∗
          (if ir.fires then
            AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
              <{ ∀∀ (σ' : State) (res : Resp), ⌜irrStep p tls lo ir σ σ' res⌝ ∗ etcdState γ σ',
                 COMM Q σ σ' res }>
          else True)) ∨
       (⌜resp = null ∧ srvIndef err⌝ ∗ srvErrShape err)) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial

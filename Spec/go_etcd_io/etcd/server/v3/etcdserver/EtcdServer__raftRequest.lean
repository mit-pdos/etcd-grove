/-
## `(*EtcdServer).raftRequest(ctx, r)`

**Users.** Every write entry point of `v3_server.go` (`Put`, `DeleteRange`, a write `Txn`, the lease
grant and revocation, `Alarm`, the auth methods, `Authenticate`'s token); the server's internal
requesters: the lease checkpoints (`server.go:402`, `.noop`), the alarms (`server.go:2025`,
`corrupt.go:441`, `.alarmActivate`, an update from `envUpd`), `publishV3` (`server.go:1848`,
`.publish`), the cluster version (`server.go:2344`, `.noop`), the downgrade (`adapters.go:50,56`,
`.noop`). Snippets: `examples/specreq/etcdserverreq/kv.go`, `lease.go`, `auth.go`.

**Proof sketch.** `processInternalRaftRequestOnce` (its spec); an error: the span's `RecordError`
(otel's boundary), returned (outcomes 2, 3); `result.Err`: returned (the answer's error: outcome 1
with `srvErrOf`, or outcome 2 with the update); `ctx.Value(StartTimeKey{})` and the trace's steps
(`applyResult`'s owned `traceOpt`, 4b); `result.Resp` (`irrReply`).

**Changes.** The old spec (`specs-ref`'s `EtcdServer__raftRequest.lean`) restated as
`processInternalRaftRequestOnce`'s (round 1 likewise: the message given back, `wf`, the principal
pair, the errors' shape, `backOk`: the reply of `Authenticate`'s token with its update back).

**Margin.** As `processInternalRaftRequestOnce`.
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

/-- **A request through raft**: its reply (outcome 1), or its error (outcome 1, the answer's;
outcome 2, the update given back; outcome 3). -/
def EtcdServer.raftRequest.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (p tls : Principal) (lo : Nat) (r : Loc)
    (dq : DFrac) (ir : IrrBody) (rep : Bool) (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ Context.ctxOk ctx ∗ reqCtxOk ctx ∗ reqPrin ctx p tls ∗ threadTok ∗ irrOwn r dq ir ∗
      ⌜ir.wf⌝ ∗ authLb γ lo ∗
      (if ir.fires then
          □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
            <{ ∀∀ (σ' : State) (res : Resp), ⌜irrStep p tls lo ir σ σ' res⌝ ∗ etcdState γ σ',
               COMM Q σ σ' res }>
        else True) }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"raftRequest")) (Val #ctx)) (Val #r))
  {{ (resp : GoInterface) (err : GoInterface), RET (PairV #resp #err); threadTok ∗ irrOwn r dq ir ∗
      ((∃ σ σ' res, (if ir.fires then Q σ σ' res else True) ∗
          match res with
          | .ok _ => iprop(⌜err = GoInterface.nil⌝ ∗ irrReply γ ir res resp)
          | .err e => iprop(⌜resp = GoInterface.nil ∧ srvErrOf err e⌝ ∗ srvErrShape err)) ∨
       (∃ res, ⌜ir.backOk res⌝ ∗
          match res with
          | .ok _ => iprop(⌜err = GoInterface.nil⌝ ∗ irrReply γ ir res resp ∗ (if ir.fires then
          □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
            <{ ∀∀ (σ' : State) (res : Resp), ⌜irrStep p tls lo ir σ σ' res⌝ ∗ etcdState γ σ',
               COMM Q σ σ' res }>
        else True))
          | .err _ => iprop(⌜resp = GoInterface.nil ∧ srvUnfired err⌝ ∗ srvErrShape err ∗ (if ir.fires then
          □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
            <{ ∀∀ (σ' : State) (res : Resp), ⌜irrStep p tls lo ir σ σ' res⌝ ∗ etcdState γ σ',
               COMM Q σ σ' res }>
        else True))) ∨
       (⌜resp = GoInterface.nil ∧ srvUnfired err⌝ ∗ srvErrShape err ∗ (if ir.fires then
          □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
            <{ ∀∀ (σ' : State) (res : Resp), ⌜irrStep p tls lo ir σ σ' res⌝ ∗ etcdState γ σ',
               COMM Q σ σ' res }>
        else True)) ∨
       (⌜resp = GoInterface.nil ∧ srvIndef err⌝ ∗ srvErrShape err)) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial

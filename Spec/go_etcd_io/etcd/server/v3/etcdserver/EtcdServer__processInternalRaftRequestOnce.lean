/-
## `(*EtcdServer).processInternalRaftRequestOnce(ctx, r)` (the proposal)

**Users.** `raftRequest` (every write path), `Compact` (`v3_server.go:392`). Concurrent callers.
Snippets: every write snippet of `examples/specreq/etcdserverreq/` (through `raftRequest`).

**Proof sketch.** `getAppliedIndex`/`getCommittedIndex` (atomics, any values), `exceedsRequestLimit`
(2e's spec; `ErrTooManyRequests`: outcome 2, nothing proposed); `r.Header = {ID: s.reqIDGen.Next()}`
(`IdUtil.Generator.Next.spec`: `idFresh γi id`, the member's generator in `isServer`); unless
`Authenticate`, `AuthInfoFromCtx(ctx)` (`AuthInfoFromCtx.spec`: `who`'s name and the auth revision
into the header, or an invalid token: outcome 2); `proto.Marshal(r)` (protobuf's boundary, at the
depth premise: `irrOwn` gives bytes every member's apply decodes back to `ir` with this header; its
error: outcome 2); `len(data) > MaxRequestBytes`: `ErrRequestTooLarge` (outcome 2); `id` (`r.ID` is
`0`: `irrOwn`'s); `s.w.Register(id)` (`Wait.list.Register.spec`, its `waitTok` from the cluster's
invariant, where `idFresh` shows `id` was never registered: `Wait.waitToks_take`; the receive half
`waitRecv`); `context.WithTimeout(ctx, ReqTimeout())`; **the proposal**: `s.r.Propose(cctx, data)`
(R1's `node.Propose.spec`, through the raft wrapper, 2d) with the update over `committedOps` that the
cluster's invariant builds from the caller's (2d, `propose_upd`, `req/`): at the entry's commit it
appends the entry to the history (`histAt`), fires the caller's update at `σ` with the answer the
apply will compute (`answered γ k id res`; an apply refusal of outcome 2, `ErrAuthOldRevision`,
fires nothing and keeps the update for the waiter), and deposits the waiter's share for `id` (the
wait registry's `P id`). A `Propose` error: `Trigger(id, nil)` with `waitRecv` (`Wait.list.
Trigger.spec`), the error unsettled (raft's `propErr`: dropped or the context's: the update may be
in raft). The `select`: `ch` (`Wait.waitRecv_recv`: the apply thread's `*apply.Result` for the
entry, `applyResult` with the fired `Q` or the update back); `cctx.Done()` (`Trigger(id, nil)`,
`parseProposeCtxErr`: unsettled); `s.done` (`ErrStopped`: unsettled). Deferred: `cancel`, the
metrics (4b's prometheus boundary).

**Changes.** The old spec (`specs-ref`'s `EtcdServer__processInternalRaftRequestOnce.lean`: the
request's names `ρ`, `idCred`, the proposal's ghost data, the outcome model) restated over W0's
state: the caller's update over `etcdState` by `irrStep`, the three outcomes, the result as
`applyResult`.

**Margin.** A result of outcome 1 for an apply refusal other than a stale auth revision (the quota's
`ErrNoSpace`, `ErrCorrupt`) is fired (a refusal is a `Step`); the code would allow giving it back.
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

/-- **Proposes `ir` and waits for its result**: the apply's result with the update fired at the
entry's commit (outcome 1), or with the update given back for an apply refusal (outcome 2); an
error before proposing, the update given back; an unsettled error. -/
def EtcdServer.processInternalRaftRequestOnce.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (who : Principal) (r : Loc) (ir : IrrBody)
    (rep : Bool) (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ Context.ctxOk ctx ∗ reqPrin ctx who ∗ threadTok ∗ irrOwn r ir ∗
      ⌜ir.depthOk⌝ ∗
      (if ir.fires then
          □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
            <{ ∀∀ (σ' : State) (res : Resp), ⌜irrStep who ir σ σ' res⌝ ∗ etcdState γ σ',
               COMM Q σ σ' res }>
        else True) }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"processInternalRaftRequestOnce")) (Val #ctx)) (Val #r))
  {{ (x : Loc) (err : GoInterface), RET (PairV #x #err); threadTok ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ σ σ' res, (if ir.fires then Q σ σ' res else True) ∗
          applyResult γ x ir res) ∨
       (⌜err = GoInterface.nil⌝ ∗ (∃ e, ⌜e.refusal = true⌝ ∗ applyResult γ x ir (.err e)) ∗
          (if ir.fires then
          □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
            <{ ∀∀ (σ' : State) (res : Resp), ⌜irrStep who ir σ σ' res⌝ ∗ etcdState γ σ',
               COMM Q σ σ' res }>
        else True)) ∨
       (⌜x = null ∧ srvUnfired err⌝ ∗ (if ir.fires then
          □?rep AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
            <{ ∀∀ (σ' : State) (res : Resp), ⌜irrStep who ir σ σ' res⌝ ∗ etcdState γ σ',
               COMM Q σ σ' res }>
        else True)) ∨
       ⌜x = null ∧ srvIndef err⌝) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial

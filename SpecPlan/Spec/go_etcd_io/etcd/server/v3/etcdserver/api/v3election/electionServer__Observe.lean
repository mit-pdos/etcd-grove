/-
## `(*electionServer).Observe(req, stream)` (`election.go:68-81`): translated

**Users.** The Election service's `Observe` RPC (`etcdctl elect --listen`, `v3electionpb`
clients), through the generated `_Election_Observe_Handler` (3h's `observeStreamAt`).

**Proof sketch.** `stream.Context()` (3h's `observeStream_context`: the run's context `ctx`,
`ctxOk`); `session(ctx, -1)` (`electionServer.session.spec`: lease `-1` grants nothing, so the
read permission `etcdPerm γ Ts` with `readEff` suffices; then `Orphan`); `NewElection(s, name)`
(1d: the prefix `name ++ "/"`); `e.Observe(ctx)` (1d's `Election.Observe.spec`: `observeAt ch γ
(name ++ "/") σ0`, from `etcdPeek`). The loop, while `ctx.Err() == nil` (`Context.Err.spec`): a
`select` on `ctx.Done()` and the channel (1d's `observeAt_recvAu`): closed, `nil`; a value, a
`GetResponse` with `m.kvs = [_]` (so `resp.Kvs[0]` does not panic: the point of 1d's post), the
reply built (3h's `resp_fold`: the header and the key-value read-only) and sent (3h's
`observeStream_send`: an error returned). The loop carries `observeAt` and `observeStreamAt`.

**Changes**: new (A3 completeness F3: translated with a body, no spec before; second pass, now
that 3h gives the stream's vocabulary).

**Margin.** What the sent replies say (1d's `ObservedAt` facts per value) is not stated: the
stream's `Send` carries only the reply's model, so a client of this RPC sees nothing more; the
error is not classified.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace V3election

open Iris Iris.BI EtcdModel ClientV3 Concurrency

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3election.Assumptions]

/-- **Streams the leader of `name`'s changes** to `ss` until the client goes away or the
observation ends; no panic. -/
def electionServer.Observe.spec : Prop :=
  ∀ (es c : Loc) (γ : Cluster) (dflt who : Principal) (ss ctx : GoInterface) (σ0 : State)
    (req : Loc) (name : GoString) (Ts : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election ∗ isElectionServer es c ∗ ClientV3.isClient c γ dflt ∗
      V3electionpb.observeStreamAt ss ctx ∗ ClientV3.ctxPrin dflt ctx who ∗ etcdLb γ σ0 ∗
      leaderReq req name ∗ etcdPeek γ ∗ etcdPerm γ Ts ∗ ⌜effIn (fun σ σ' => readEff σ σ') Ts⌝ }}
    (App (App (Val (es @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer.ty @!! go!"Observe")) (Val #req)) (Val #ss))
  {{ (err : GoInterface), RET #err; V3electionpb.observeStreamAt ss ctx }}

end spec

end V3election
end EtcdGrove
end Perennial

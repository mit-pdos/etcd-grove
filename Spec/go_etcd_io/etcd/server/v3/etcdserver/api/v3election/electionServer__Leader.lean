/-
## `(*electionServer).Leader(ctx, req)` (`election.go:83-92`): translated

**Users.** The `Leader` RPC. **Proof sketch.** `session` (1d's `NewSession.spec` with the request's lease and context:
`etcdPerm γ Ts`'s read or grant; then `Orphan`: the keep-alive ends), then 1d's method on a
`NewElection`/`ResumeElection` of the request's name and key, with the lent permission
`etcdLent γ T P ∗ P` 1d's method takes. (lease `-1`: no grant) `Election.Leader.spec` (over `etcdPeek`):
an oldest key under the name at a reached state (`firstCreate`), or `ErrElectionNoLeader`.
**Changes**: from `specs-ref`'s `electionServer__Leader.lean`.
Changes: verify-round: the prefix is `name ++ "/"` (`NewElection`'s; A3 completeness F1, A8
provability F6: `firstCreate name` claimed no older key under `name`, including `name ++ "z"`); the
state reached from `σ0`; the message is 3h's. **Margin.** As 1d's.

**The principal** (round 1, completeness F9): the in-process client (`v3client.New(s)`, default
principal `dflt`: none) forwards each call's token, so the call's principal is the context's `who`
(`ClientV3.ctxPrin dflt ctx who`), the effects under it, as 1d's specs state them. `v3client.New`'s
spec (an `isClient … none` from `isServer`) is requested of 1c (`req/…client_v3.md`, "from 2e,
round 1").
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3election.Api

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

/-- **The current leader of `name`**: an oldest key under `name ++ "/"` at a reached state. -/
def electionServer.Leader.spec : Prop :=
  ∀ (es c : Loc) (γ : Cluster) (dflt who : Principal) (ctx : GoInterface) (σ0 : State) (req : Loc) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election ∗ isElectionServer es c ∗ ClientV3.isClient c γ dflt ∗ Context.ctxOk ctx ∗ ClientV3.ctxPrin dflt ctx who ∗ etcdLb γ σ0 ∗ leaderReq req name ∗ etcdPeek γ }}
    (App (App (Val (es @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer.ty @!! go!"Leader")) (Val #ctx)) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (v : KV) (σ : State), leaderResp resp v ∗ etcdLb γ σ ∗
          ⌜Reach σ0 σ ∧ firstCreate (name ++ go!"/") σ.kv.store [v]⌝) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end V3election
end EtcdGrove
end Perennial

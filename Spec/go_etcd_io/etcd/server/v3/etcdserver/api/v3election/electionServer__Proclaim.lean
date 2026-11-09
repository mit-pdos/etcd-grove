/-
## `(*electionServer).Proclaim(ctx, req)` (`election.go:52-66`): translated

**Users.** The `Proclaim` RPC. `ErrMissingLeaderKey` without a leader key.

**Proof sketch.** `session` (1d's `NewSession.spec` with the request's lease and context:
`etcdPerm γ Ts`'s read or grant; then `Orphan`: the keep-alive ends), then 1d's method on a
`NewElection`/`ResumeElection` of the request's name and key, with the lent permission
`etcdLent γ T P ∗ P` 1d's method takes. `Election.Proclaim.spec` (a put of the key if its create revision is still the leader key's;
else `ErrElectionNotLeader`).

**Changes** (from `specs-ref`'s `electionServer__Proclaim.lean`): over 1d's facts.
**Margin.** As 1d's.

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

/-- **Proclaims `value`** as the leader `lk`: the key holds it at a reached state. -/
def electionServer.Proclaim.spec : Prop :=
  ∀ (es c : Loc) (γ : Cluster) (dflt who : Principal) (ctx : GoInterface) (σ0 : State) (req : Loc) (lk : Option LeaderKeyM) (value : GoString)
    (Ts T : State → State → Prop) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election ∗ isElectionServer es c ∗ ClientV3.isClient c γ dflt ∗ Context.ctxOk ctx ∗ ClientV3.ctxPrin dflt ctx who ∗ etcdLb γ σ0 ∗ proclaimReq req lk value ∗ etcdPerm γ Ts ∗
      ⌜∀ x, lk = some x → effIn (fun σ σ' => readEff σ σ' ∨ (x.lease = W64 0 ∧ grantEff 60 σ σ')) Ts ∧
        ∀ l : Int, effIn (putEff (fun k => k = x.key) (fun v => v = value) l) T⌝ ∗ etcdLent γ T P ∗ P }}
    (App (App (Val (es @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer.ty @!! go!"Proclaim")) (Val #ctx)) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (x : LeaderKeyM) (σ : State), ⌜lk = some x⌝ ∗ proclaimResp resp ∗
          etcdLb γ σ ∗ ⌜∃ r, σ.kv.store x.key = some r ∧ r.value = value ∧ r.createRev = uint.nat x.rev⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end V3election
end EtcdGrove
end Perennial

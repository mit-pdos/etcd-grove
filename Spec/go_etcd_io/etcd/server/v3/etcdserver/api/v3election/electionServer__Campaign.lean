/-
## `(*electionServer).Campaign(ctx, req)` (`election.go:31-50`): translated

**Users.** The Election service's `Campaign` RPC (`etcdctl elect`, `v3electionpb` clients), through
2a's registration.

**Proof sketch.** `session` (1d's `NewSession.spec` with the request's lease and context:
`etcdPerm γ Ts`'s read or grant; then `Orphan`: the keep-alive ends), then 1d's method on a
`NewElection`/`ResumeElection` of the request's name and key, with the lent permission
`etcdLent γ T P ∗ P` 1d's method takes. `Election.Campaign.spec`: the key under the name created with the session's lease and
`value`, and the wait's fact (`waitedFor`).

**Changes** (from `specs-ref`'s `electionServer__Campaign.lean`, auth-on only): over 1d's facts, any
auth mode. **Margin.** The header is not stated.

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

/-- **Campaigns** for leadership of `name` with `value`: the elected key, its create revision, and the wait's fact. -/
def electionServer.Campaign.spec : Prop :=
  ∀ (es c : Loc) (γ : Cluster) (dflt who : Principal) (ctx : GoInterface) (σ0 : State) (req : Loc) (name : GoString) (lease : w64) (value : GoString)
    (Ts T : State → State → Prop) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election ∗ isElectionServer es c ∗ ClientV3.isClient c γ dflt ∗ Context.ctxOk ctx ∗ ClientV3.ctxPrin dflt ctx who ∗ etcdLb γ σ0 ∗ campaignReq req name lease value ∗ etcdPerm γ Ts ∗
      ⌜effIn (fun σ σ' => readEff σ σ' ∨ (lease = W64 0 ∧ grantEff 60 σ σ')) Ts⌝ ∗
      etcdLent γ T P ∗ P ∗ ⌜∀ l : Int, effIn (campaignEff name value l) T⌝ }}
    (App (App (Val (es @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer.ty @!! go!"Campaign")) (Val #ctx)) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (k : GoString) (cr : Nat) (l : w64) (σ : State),
          campaignResp resp (LeaderKeyM.mk name k (W64 cr) l) ∗ etcdLb γ σ ∗
          ⌜waitedFor name k cr σ⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end V3election
end EtcdGrove
end Perennial

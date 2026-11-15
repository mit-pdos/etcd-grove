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
auth mode.
Changes: verify-round: the prefix is `name ++ "/"` (`NewElection`'s; A3 completeness F1, A8
provability F6), in the effect and in `waitedFor`; the key is the session's (`sessKey`) and the
reply's lease the session's (the request's when non-zero); the value held at a reached state (1d's
`σv`); the lent token `P` given back on success (A3 completeness F7); the messages are 3h's.
**Margin.** The header is not stated; on an error `P` is not returned.

**The principal** (round 1, completeness F9): the in-process client (`v3client.New(s)`, default
principal `dflt`: none) forwards each call's token, so the call's principal is the context's `who`
(`ClientV3.ctxPrin dflt ctx who`), the effects under it, as 1d's specs state them. `v3client.New`'s
spec (an `isClient … none` from `isServer`) is requested of 1c (`req/…client_v3.md`, "from 2e,
round 1").
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

/-- **Campaigns** for leadership of `name` (the prefix `name ++ "/"`) with `value`: the elected
key (the session's), its create revision, the session's lease, and the wait's fact; the lent token
back. -/
def electionServer.Campaign.spec : Prop :=
  ∀ (es c : Loc) (γ : Cluster) (dflt who : Principal) (ctx : GoInterface) (σ0 : State) (req : Loc) (name : GoString) (lease : w64) (value : GoString)
    (Ts T : State → State → Prop) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election ∗ isElectionServer es c ∗ ClientV3.isClient c γ dflt ∗ Context.ctxOk ctx ∗ ClientV3.ctxPrin dflt ctx who ∗ etcdLb γ σ0 ∗ campaignReq req name lease value ∗ etcdPerm γ Ts ∗
      ⌜effIn (fun σ σ' => readEff σ σ' ∨ (lease = W64 0 ∧ grantEff 60 σ σ')) Ts⌝ ∗
      etcdLent γ T P ∗ P ∗ ⌜∀ l : Int, effIn (campaignEff (name ++ go!"/") value l) T⌝ }}
    (App (App (Val (es @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer.ty @!! go!"Campaign")) (Val #ctx)) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ P ∗ ∃ (k : GoString) (cr : Nat) (id : w64) (σ σv : State),
          campaignResp resp ⟨name, k, W64 cr, id⟩ ∗ etcdLb γ σ ∗ etcdLb γ σv ∗
          ⌜Reach σ0 σ ∧ Reach σ0 σv ∧ (lease ≠ W64 0 → id = lease) ∧
            k = sessKey (name ++ go!"/") (sint.Z id) ∧ waitedFor (name ++ go!"/") k cr σ ∧
            ∃ r, σv.kv.store k = some r ∧ r.createRev = cr ∧ r.value = value⌝) ∨
      ⌜err ≠ GoInterface.nil⌝ }}

end spec

end V3election
end EtcdGrove
end Perennial

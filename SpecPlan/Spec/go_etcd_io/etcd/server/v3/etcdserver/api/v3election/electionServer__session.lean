/-
## `(*electionServer).session(ctx, lease)` (`election.go:110-121`): translated

**Users.** Every method of the service. **Proof sketch.** 1d's `NewSession.spec` with
`WithLease(lease)`, `WithContext(ctx)` (a lease of `0` is granted, TTL 60), then
`Session.Orphan.spec`. **Changes** (from `specs-ref`'s `electionServer__session.lean`): over 1d's
session. **Margin.** The lease granted at `0` is not named.

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

/-- **A session over `lease`** (granted at `0`), its keep-alive ended. -/
def electionServer.session.spec : Prop :=
  ∀ (es c : Loc) (γ : Cluster) (dflt who : Principal) (ctx : GoInterface) (σ0 : State) (lease : w64) (Ts : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election ∗ isElectionServer es c ∗ ClientV3.isClient c γ dflt ∗ Context.ctxOk ctx ∗ ClientV3.ctxPrin dflt ctx who ∗ etcdLb γ σ0 ∗ etcdPerm γ Ts ∗
      ⌜effIn (fun σ σ' => readEff σ σ' ∨ (lease = W64 0 ∧ grantEff 60 σ σ')) Ts⌝ }}
    (App (App (Val (es @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer.ty @!! go!"session")) (Val #ctx)) (Val #lease))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ id : w64, isSession s c γ id ∗ ⌜lease ≠ W64 0 → id = lease⌝) ∨
      ⌜s = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end V3election
end EtcdGrove
end Perennial

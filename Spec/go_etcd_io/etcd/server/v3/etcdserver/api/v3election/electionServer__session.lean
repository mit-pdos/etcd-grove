/-
## `(*electionServer).session(ctx, lease)` (`election.go:110-121`): translated

**Users.** Every method of the service. **Proof sketch.** 1d's `NewSession.spec` with
`WithLease(lease)`, `WithContext(ctx)` (a lease of `0` is granted, with TTL 60), then
`Session.Orphan.spec`. **Changes** (from `specs-ref`'s `electionServer__session.lean`): over 1d's
session. **Margin.** The lease granted at `0` is not named.
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

/-- **A session over `lease`** (granted at `0`), its keep-alive ended. -/
def electionServer.session.spec : Prop :=
  ∀ (es c : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (lease : w64)
    (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election ∗ isElectionServer es c ∗ ClientV3.isClient c γ who ∗ Context.ctxOk ctx ∗ ClientV3.ctxPrin ctx who ∗
      etcdPerm γ T ∗ ⌜effIn (fun σ σ' => readEff σ σ' ∨ (lease = W64 0 ∧ grantEff 60 σ σ')) T⌝ ∗
      threadTok }}
    (App (App (Val (es @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer.ty @!! go!"session")) (Val #ctx)) (Val #lease))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ id : w64, isSession s γ who id ∗ ⌜lease ≠ W64 0 → id = lease⌝) ∨
      ⌜s = null ∧ err ≠ GoInterface.nil⌝ }}

end spec

end V3election
end EtcdGrove
end Perennial

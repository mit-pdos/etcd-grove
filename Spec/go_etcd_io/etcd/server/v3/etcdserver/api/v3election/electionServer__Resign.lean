/-
## `(*electionServer).Resign(ctx, req)` (`election.go:94-108`): translated

**Users.** The `Resign` RPC. **Proof sketch.** `session` (`NewSession` with the request's lease and context, 1d's
`NewSession.spec`: the permission's read or grant, a `threadTok`; then `Orphan`: the keep-alive
ends), then 1d's method on a `NewElection`/`ResumeElection` of the request's name and key. `Election.Resign.spec` (a delete of the key if its create revision
is still the leader key's). **Changes**: from `specs-ref`'s `electionServer__Resign.lean`.
**Margin.** The deletion is not stated (the key may have expired already).
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

/-- **Resigns** the leader `lk`. -/
def electionServer.Resign.spec : Prop :=
  ∀ (es c : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (req : Loc)
    (lk : Option LeaderKeyM) (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election ∗ isElectionServer es c ∗ ClientV3.isClient c γ who ∗ Context.ctxOk ctx ∗ ClientV3.ctxPrin ctx who ∗ resignReq req lk ∗
      etcdPerm γ T ∗ ⌜∀ x, lk = some x → effIn (fun σ σ' => readEff σ σ' ∨ (x.lease = W64 0 ∧ grantEff 60 σ σ')) T ∧
        effIn (delEff (fun k => x.name <+: k)) T⌝ ∗ threadTok }}
    (App (App (Val (es @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer.ty @!! go!"Resign")) (Val #ctx)) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ resignResp resp) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end V3election
end EtcdGrove
end Perennial

/-
## `(*electionServer).Resign(ctx, req)` (`election.go:94-108`): translated

**Users.** The `Resign` RPC. **Proof sketch.** `session` (1d's `NewSession.spec` with the request's lease and context:
`etcdPerm γ Ts`'s read or grant; then `Orphan`: the keep-alive ends), then 1d's method on a
`NewElection`/`ResumeElection` of the request's name and key, with the lent permission
`etcdLent γ T P ∗ P` 1d's method takes. `Election.Resign.spec` (a delete of the key if its create revision
is still the leader key's). **Changes**: from `specs-ref`'s `electionServer__Resign.lean`.
**Margin.** The deletion is not stated (the key may have expired already).

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

/-- **Resigns** the leader `lk`. -/
def electionServer.Resign.spec : Prop :=
  ∀ (es c : Loc) (γ : Cluster) (dflt who : Principal) (ctx : GoInterface) (σ0 : State) (req : Loc) (lk : Option LeaderKeyM) (Ts T : State → State → Prop) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election ∗ isElectionServer es c ∗ ClientV3.isClient c γ dflt ∗ Context.ctxOk ctx ∗ ClientV3.ctxPrin dflt ctx who ∗ etcdLb γ σ0 ∗ resignReq req lk ∗ etcdPerm γ Ts ∗
      ⌜∀ x, lk = some x → effIn (fun σ σ' => readEff σ σ' ∨ (x.lease = W64 0 ∧ grantEff 60 σ σ')) Ts ∧
        effIn (delEff (fun k => k = x.key)) T⌝ ∗ etcdLent γ T P ∗ P }}
    (App (App (Val (es @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer.ty @!! go!"Resign")) (Val #ctx)) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ resignResp resp) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end V3election
end EtcdGrove
end Perennial

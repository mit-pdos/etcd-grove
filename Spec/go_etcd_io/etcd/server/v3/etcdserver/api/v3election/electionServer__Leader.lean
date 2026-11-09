/-
## `(*electionServer).Leader(ctx, req)` (`election.go:83-92`): translated

**Users.** The `Leader` RPC. **Proof sketch.** `session` (`NewSession` with the request's lease and context, 1d's
`NewSession.spec`: the permission's read or grant, a `threadTok`; then `Orphan`: the keep-alive
ends), then 1d's method on a `NewElection`/`ResumeElection` of the request's name and key. (lease `-1`: no grant) `Election.Leader.spec`: the oldest key
under the name at a reached state (`firstCreate`), or `ErrElectionNoLeader`.
**Changes**: from `specs-ref`'s `electionServer__Leader.lean`. **Margin.** As 1d's.
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

/-- **The current leader of `name`**: an oldest key under it at a reached state. -/
def electionServer.Leader.spec : Prop :=
  ∀ (es c : Loc) (γ : Cluster) (dflt who : Principal) (ctx : GoInterface) (req : Loc)
    (name : GoString) (T : State → State → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3election ∗ isElectionServer es c ∗ ClientV3.isClient c γ dflt ∗ Context.ctxOk ctx ∗ ClientV3.ctxPrin dflt ctx who ∗ leaderReq req name ∗
      etcdPerm γ T ∗ ⌜effIn readEff T⌝ ∗ threadTok }}
    (App (App (Val (es @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3election.electionServer.ty @!! go!"Leader")) (Val #ctx)) (Val #req))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (v : KV) (σ : State), leaderResp resp v ∗ etcdLb γ σ ∗
          ⌜firstCreate name σ.kv.store [v]⌝) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end V3election
end EtcdGrove
end Perennial

/-
**What the names-only proposers propose** (D19c, option (a), 2026-10-18; `notes/decisions.md`,
D19c). Lean-first (no Rocq counterpart).

Besides the request path (`EtcdServer.Put`/`DeleteRange`/`Txn`, whose proposals carry their
shapes, `reqPropOk`), two goroutines `Start` attaches propose through `s.raftRequest`, and their
specs are trust-boundary contracts (names-only, `server.go`):

* `publishV3(timeout)` proposes `InternalRaftRequest{ClusterMemberAttrSet: …}` (the member's name
  and client URLs), retrying until it succeeds or the server stops;
* `monitorClusterVersions()` (on the leader) proposes, through `updateClusterVersionV3`,
  `InternalRaftRequest{ClusterVersionSet: {Ver: v.String()}}` with `v` a `semver.Version` the
  monitor decided (`decideClusterVersion`), whose `String()` parses back (`semverValid`).

Their contracts take `srvMonitorPermit s E ρ`: the server's request path and the proposals'
permission (`reqPropOk`, with a trivial result) for exactly those requests, a plain non-write
request of one of the two kinds with no range end `[0]` (no range, delete or transaction field
set) and, for a version, a valid one. So the committed entries they produce have the shapes the KV
invariant keeps (`rqShape`: `rqOk` asks nothing of a member's attributes, and a valid version of
`ClusterVersionSet`). Until D19c their contracts took only the package's initialization (their
proposals were not in the model).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-- **The requests the monitors propose** (pure): a member's attributes, or a valid cluster
version, with no range end `[0]`. -/
def monitorReq (rq : apply.IRRModel) : Prop :=
  irrNoZeroEnd rq ∧
    (apply.dispatchKind rq = .clusterMemberAttrSet ∨
      (apply.dispatchKind rq = .clusterVersionSet ∧
        ∀ v, rq.clusterVersionSet = some v → apply.semverValid v))

/-- A monitor's request has a good shape. -/
theorem rqShape_of_monitorReq (rq : apply.IRRModel) (h : monitorReq rq) : rqShape rq := by
  obtain ⟨-, hk⟩ := h
  refine ⟨fun on => ?_, fun log _ => ?_⟩
  · unfold apply.dispatchOk
    rcases hk with hk | ⟨hk, -⟩ <;> rw [hk] <;> exact ⟨by decide, by decide, fun h => by cases h⟩
  · unfold apply.rqOk
    rcases hk with hk | ⟨hk, hv⟩ <;> rw [hk]
    · trivial
    · exact hv

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **What the monitors may propose** (persistent; see the file header): the server's request
path, and the proposal's permission for a monitor's request. -/
def srvMonitorPermit (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) : IProp GF :=
  iprop(isServerReq s E ρ ∗
    □ ∀ rq : apply.IRRModel, ⌜monitorReq rq⌝ -∗ reqPropOk ρ.kv rq (fun _ => iprop(True)))

instance srvMonitorPermit_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    Persistent (srvMonitorPermit (GF := GF) s E ρ) := by
  unfold srvMonitorPermit; infer_instance

/-- The monitors' permission, from the server's request path. -/
theorem srvMonitorPermit_of (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isServerReq (GF := GF) s E ρ ⊢ srvMonitorPermit s E ρ := by
  iintro #H
  iunfold srvMonitorPermit
  iframe H
  iintro !> %rq %hrq
  iunfold reqPropOk
  ileft
  ipureintro
  have hs := rqShape_of_monitorReq rq hrq
  obtain ⟨hz, hk⟩ := hrq
  have hk' : apply.dispatchKind rq = .clusterMemberAttrSet ∨
      apply.dispatchKind rq = .clusterVersionSet := by
    rcases hk with hk | ⟨hk, -⟩
    · exact Or.inl hk
    · exact Or.inr hk
  refine ⟨?_, ?_, hz, hs, rfl⟩
  · unfold plainReq; rcases hk' with hk' | hk' <;> rw [hk'] <;> trivial
  · unfold writeKind; rcases hk' with hk' | hk' <;> rw [hk'] <;> decide

end defs

end EtcdGrove
end Perennial

/-
**The names-only proposers' permission in either auth mode** (the auth plan's E3zb, 2026-10-28;
`InvMonitors.lean`'s `srvMonitorPermit`, for a server started with auth on): `publishV3` and
`monitorClusterVersions` propose only cluster requests (`monitorReq`), whose header the server
stamps; in the mode `on` their proposal permission is `reqPropOkOn`'s first case (a non-write
request needing no permission: `kvShapeAll` holds of a request with no permissions). Lean-first
(no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvMonitors
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- A monitor's request is a plain non-write request of a good shape (`srvMonitorPermit_of`'s). -/
theorem monitorReq_prop (rq : apply.IRRModel) (h : monitorReq rq) :
    plainReq rq ∧ ¬ writeKind (apply.dispatchKind rq) ∧ irrNoZeroEnd rq ∧ rqShape rq ∧
      kvShapeAll rq := by
  have hs := rqShape_of_monitorReq rq h
  obtain ⟨hz, hna, hns, hk⟩ := h
  have hk' : apply.dispatchKind rq = .clusterMemberAttrSet ∨
      apply.dispatchKind rq = .clusterVersionSet := by
    rcases hk with hk | ⟨hk, -⟩
    · exact Or.inl hk
    · exact Or.inr hk
  refine ⟨?_, ?_, hz, hs, ?_⟩
  · refine ⟨?_, putgetKind_cluster rq hk'⟩
    unfold plainCover; rcases hk' with hk' | hk' <;> rw [hk'] <;> exact ⟨hns, hna⟩
  · unfold writeKind; rcases hk' with hk' | hk' <;> rw [hk'] <;> decide
  · unfold kvShapeAll reqPerms
    rcases hk' with hk' | hk' <;> rw [hk'] <;> simp

/-- A monitor's request with the header the server stamps is a monitor's request. -/
theorem monitorReq_withHeader (rq : apply.IRRModel) (hm : apply.HeaderModel) :
    monitorReq (apply.withHeader rq hm) ↔ monitorReq rq := Iff.rfl

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The monitors' permission in the auth mode `on`** (persistent; `srvMonitorPermit`'s): the
request view in the mode, and the proposal permission in the mode (`reqPropOkM`, with a trivial
result) for the monitors' requests. -/
def srvMonitorPermitM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) : IProp GF :=
  iprop(isServerReqM on s E ρ ∗
    □ ∀ (rq : apply.IRRModel) (Gb : apply.HeaderModel → IProp GF), ⌜monitorReq rq⌝ -∗
      reqPropOkM on ρ.raft ρ.kv Gb rq (fun _ _ => iprop(True)))

/-- The monitors' permission in either mode, from the server's request path in the mode. -/
theorem srvMonitorPermitM_of (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isServerReqM (GF := GF) on s E ρ ⊢ srvMonitorPermitM on s E ρ := by
  iintro #H
  iunfold srvMonitorPermitM
  iframe H
  iintro !> %rq %Gb %hrq
  cases on
  · iapply (reqPropOkM_of_false ρ.raft ρ.kv Gb rq (fun _ => iprop(True)))
    iunfold reqPropOk
    ileft
    ipureintro
    obtain ⟨h1, h2, h3, h4, -⟩ := monitorReq_prop rq hrq
    exact ⟨h1, h2, h3, h4, rfl⟩
  · iunfold reqPropOkM
    iintro %hm
    iunfold reqPropOkOn
    ileft
    ipureintro
    obtain ⟨h1, h2, h3, h4, h5⟩ := monitorReq_prop (apply.withHeader rq hm)
      ((monitorReq_withHeader rq hm).2 hrq)
    exact ⟨h1, h2, h3, h4, h5, rfl⟩

end defs

end EtcdGrove
end Perennial

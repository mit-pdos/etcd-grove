/-
**The names-only proposers' permission in either auth mode** (the auth plan's E3zb, 2026-10-28;
until the cluster-rows stage, 2026-11-02, beside `InvMonitors.lean`'s mode-off `srvMonitorPermit`,
since deleted): `publishV3` and
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

/-- A monitor's request is a plain non-write request of a good shape (`srvMonitorPermitM_of`'s). -/
theorem monitorReq_prop (lid : w64) (rq : apply.IRRModel) (h : monitorReq lid rq) :
    plainReq rq ∧ ¬ writeKind (apply.dispatchKind rq) ∧ irrNoZeroEnd rq ∧ rqShape rq ∧
      kvShapeAll rq := by
  have hs := rqShape_of_monitorReq lid rq h
  obtain ⟨⟨hz, hna, hns, hk⟩, -⟩ := h
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
theorem monitorReq_withHeader (lid : w64) (rq : apply.IRRModel) (hm : apply.HeaderModel) :
    monitorReq lid (apply.withHeader rq hm) ↔ monitorReq lid rq := Iff.rfl

/-- A monitor's request names the server's own id, a voter: its attribute fact. -/
theorem attrIdOk_of_monitorReq (S : GSet w64) (lid : w64) (rq : apply.IRRModel)
    (h : monitorReq lid rq) (hl : lid ∈ S) : attrIdOk S rq := by
  intro _
  exact ⟨h.1.1, fun a ha => by rw [h.2.1 a ha]; exact hl⟩

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The monitors' permission in the auth mode `on`** (persistent): the request view in the mode,
the server's id field `lid` (read-only; 2026-11-02, the cluster-rows stage), and the proposal
permission in the mode (`reqPropOkM`, with a trivial result) for the monitors' requests naming it. -/
def srvMonitorPermitM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) : IProp GF :=
  iprop(isServerReqM on s E ρ ∗ ∃ lid : w64, srvMemberIDAddr s ↦□ lid ∗
    □ ∀ (rq : apply.IRRModel) (Gb : apply.HeaderModel → IProp GF), ⌜monitorReq lid rq⌝ -∗
      reqPropOkM on ρ.raft ρ.kv Gb rq (fun _ _ => iprop(True)))

/-- The monitors' permission in either mode, from the server's request path, its id field and
that the id is a voter of raft's configuration (`isServerBuilt`'s, at `Start`; 2026-11-02, the
cluster-rows stage). -/
theorem srvMonitorPermitM_of (on : Bool) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (lid : w64)
    (hl : lid ∈ ρ.raft.raft.cfg) :
    isServerReqM (GF := GF) on s E ρ ∗ srvMemberIDAddr s ↦□ lid ⊢ srvMonitorPermitM on s E ρ := by
  iintro ⟨#H, #Hid⟩
  iunfold srvMonitorPermitM
  iframe H
  iexists lid
  iframe Hid
  iintro !> %rq %Gb %hrq
  have hat := attrIdOk_of_monitorReq _ lid rq hrq hl
  cases on
  · iapply (reqPropOkM_of_false ρ.raft ρ.kv Gb rq (fun _ => iprop(True)) hat)
    iapply reqPropOk_of_W
    iunfold reqPropOkW
    ileft
    ipureintro
    obtain ⟨h1, h2, h3, h4, -⟩ := monitorReq_prop lid rq hrq
    exact ⟨h1, h2, h3, h4, rfl⟩
  · iunfold reqPropOkM
    isplitl
    rotate_left
    · ipureintro; exact hat
    iintro %hm
    iunfold reqPropOkOn
    ileft
    ipureintro
    obtain ⟨h1, h2, h3, h4, h5⟩ := monitorReq_prop lid (apply.withHeader rq hm)
      ((monitorReq_withHeader lid rq hm).2 hrq)
    exact ⟨h1, h2, h3, h4, h5, rfl⟩

end defs

end EtcdGrove
end Perennial

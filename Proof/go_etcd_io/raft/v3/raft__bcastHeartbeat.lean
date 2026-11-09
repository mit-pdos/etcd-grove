/-
Port of election_proof/proof_raft__bcastHeartbeat.v.

raft v3.7 (stage R4): compiles as ported (imports only).
-/
module

public import Spec.go_etcd_io.raft.v3.raft__bcastHeartbeat
public import Spec.go_etcd_io.raft.v3.readOnly__heartbeatCtx
public import Spec.go_etcd_io.raft.v3.raft__bcastHeartbeatWithCtx
public import Proof.go_etcd_io.raft.v3.TracedUntraced

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.readOnly` through `ownRaftPhysC_readOnly`, `heartbeatCtx` on the object it hands
out, the object back unchanged; then `bcastHeartbeatWithCtx` with the context: `nil`
for an empty queue, else the position, made read-only (2026-10-12). -/
theorem raft.bcastHeartbeat.wp_proof
    (wp_readOnly_heartbeatCtx : readOnly.heartbeatCtx.spec (GF := GF) (hG := hG))
    (wp_raft_bcastHeartbeatWithCtx : raft.bcastHeartbeatWithCtx.spec (GF := GF) (hG := hG)) :
    raft.bcastHeartbeat.spec (GF := GF) (hG := hG) := by
  intro c r id s G Hlead Htz
  wp_start as Hphys
  iNamed Hphys
  icases ownRaftPhysC_readOnly c r id s $$ Hphys with ⟨%ro, Hrof, Hro, Hback⟩
  wp_auto
  wp_apply wp_readOnly_heartbeatCtx $$ [$Hro] as %sl ⟨Hro, Hsl⟩
  ihave Hphys := Hback $$ %ro %_ Hrof Hro
  ihave Hphys := ownRaftPhysC_eq c r id _ s rfl $$ Hphys
  icases Hsl with (⟨%Hpend, %Hsl⟩ | ⟨%Hne, Hsl, -⟩)
  · subst Hsl
    rw [show hbCtx s.rd.ro = [] by unfold hbCtx; simp [Hpend]]
    wp_apply wp_raft_bcastHeartbeatWithCtx _ _ _ _ _ [] G Hlead Htz $$ [$Hphys HG]
      as %ms %pvs ⟨Hphys, %Hms, %Hmm, HG⟩
    · isplitr
      · iapply ownSlice_nil
      iframe Hgate HG
    iapply HΦ
    iframe Hphys HG
    ipureintro
    refine ⟨fun m Hm => ⟨(Hms m Hm).1, ?_⟩, Hmm⟩
    rw [(Hms m Hm).2]
  · imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
    rw [show hbCtx s.rd.ro = u64Le (readonlyPosition s.rd.ro) by unfold hbCtx; simp [Hne]]
    wp_apply wp_raft_bcastHeartbeatWithCtx _ _ _ _ _ _ G Hlead Htz $$ [$Hphys $Hsl HG]
      as %ms %pvs ⟨Hphys, %Hms, %Hmm, HG⟩
    · iframe Hgate HG
    iapply HΦ
    iframe Hphys HG
    ipureintro
    refine ⟨fun m Hm => ⟨(Hms m Hm).1, ?_⟩, Hmm⟩
    rw [(Hms m Hm).2]

end proof

end EtcdGrove
end Perennial

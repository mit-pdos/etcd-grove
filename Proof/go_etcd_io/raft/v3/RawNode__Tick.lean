/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Tick
public import Spec.go_etcd_io.raft.v3.raft__tickHeartbeat
-- `Step.commit_mono`
public import Proof.go_etcd_io.raft.v3.Protocol.Facts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.tick` is one of the two tick functions (`TickFnOk`, since `r.tick` is set:
`NStateWf`); either one's `TickStep` keeps `ownRawNode` but for the term. -/
theorem RawNode.Tick.wp_proof
    (wp_tickElection : raft.tickElection.spec (GF := GF) (hG := hG))
    (wp_tickHeartbeat : raft.tickHeartbeat.spec (GF := GF) (hG := hG)) :
    RawNode.Tick.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs Hterm Hflw
  wp_start as H
  iNamed H
  iNamed Hrn
  wp_auto
  have Htc1 : uint.Z s.term + 1 ≤ uint.Z s.gh.tc := by rw [← Htrm, ← Hpvoff.2.1]; exact Hterm
  have Hnw : uint.Z s.term + 1 < 2 ^ 64 := by have : uint.Z s.gh.tc < 2 ^ 64 := by word
                                              omega
  wp_apply raft.wp_load_tickC cf rnv.raft' id s Hwf.2 $$ Hphys as %f ⟨Hphys, %Hf⟩
  icases ownRaftPhysC_preFacts cf rnv.raft' id s (Hpvoff.dyn ⟨rs.capplied, rs.cfg, fp⟩) $$ Hphys with ⟨%Hpf, Hphys⟩
  rcases Hf with rfl | rfl
  all_goals first
    | wp_apply wp_tickElection cf _ γ rnv.raft' id s
        Hnw (fun _ => Htc1) Hwf (Hrnfl.1 Hflw)
        Hpf.1
        $$ [$Hphys $Hghost] as %s' ⟨Hphys, Hghost, %Hwf', %Hc, %Htk⟩
    | wp_apply wp_tickHeartbeat cf _ γ rnv.raft' id s Hwf Hpf.1
        $$ [$Hphys $Hghost] as %s' ⟨Hphys, Hghost, %Hwf', %Hc, %Htk⟩
  all_goals (
    obtain ⟨⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh, Hfl', Hap'⟩, Ht1, Ht2, -, Htpc⟩ := Htk
    ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hpv Hsd $$ Hstrecs
    iapply HΦ $$ %s'.term
    isplitl
    · iapply ownRawNode_intro γ rn id { rs with term := s'.term } s' cf fp rnv sv hprev steps
        Hwf' Hin Hal
        Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
        (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, Hsd⟩ Hc Ha (tc_le_of_gh Hgh) Hstok) rfl (by rw [Hsg]; exact Hstor) ⟨fun h => by rw [Hpre]; exact Hpvoff.1 h, by rw [Hgh]; exact Hpvoff.2.1,
          by rw [Hgh]; omega, fun hp => by rw [Hgh, Htpc hp]; exact Htc1⟩
        (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
        (RNFl.keep Hrnfl Hfl' Hap' Ha)
        $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr'
    ipureintro
    rw [Htrm]
    exact ⟨Ht1, Ht2⟩)

end proof

end EtcdGrove
end Perennial

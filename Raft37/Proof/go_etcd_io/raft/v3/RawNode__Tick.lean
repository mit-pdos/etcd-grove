/- Lean-first (no Rocq counterpart). -/
module

public import Raft37.Spec.go_etcd_io.raft.v3.RawNode__Tick
public import Raft37.Spec.go_etcd_io.raft.v3.raft__tickHeartbeat
-- `Step.commit_mono`
public import Raft37.Proof.go_etcd_io.raft.v3.Protocol.Facts

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
  intro γ rn id rs Hterm
  wp_start as H
  iNamed H
  iNamed Hrn
  wp_auto
  wp_apply raft.wp_load_tickC cf rnv.raft' id s Hwf.2 $$ Hphys as %f ⟨Hphys, %Hf⟩
  icases ownRaftPhysC_preFacts cf rnv.raft' id s Hpvoff $$ Hphys with ⟨%Hpf, Hphys⟩
  rcases Hf with rfl | rfl
  all_goals first
    | wp_apply wp_tickElection cf _ γ rnv.raft' id s
        (by rw [← Htrm]; exact Hterm) Hwf (fun _ => Hpf.1)
        $$ [$Hphys $Hghost] as %s' ⟨Hphys, Hghost, %Hwf', %Hc, %Htk⟩
    | wp_apply wp_tickHeartbeat cf _ γ rnv.raft' id s Hwf (fun _ => Hpf.1)
        $$ [$Hphys $Hghost] as %s' ⟨Hphys, Hghost, %Hwf', %Hc, %Htk⟩
  all_goals (
    obtain ⟨⟨Ha, Hsn, Hu, Hpv, Hsd, Hsg, Hpre, Hgh⟩, Ht1, Ht2, -⟩ := Htk
    ihave #Hstr' := storedRecs_eq γ _ s'.logst.prev _ s'.logst.stored Hpv Hsd $$ Hstrecs
    iapply HΦ $$ %s'.term
    isplitl
    · iapply ownRawNode_intro γ rn id { rs with term := s'.term } s' cf fp rnv sv hprev steps
        Hwf' Hin Hal
        Hasync (by rw [Ha]; exact Hdlen) (by rw [Hu]; exact Hunp) (by rw [Hsn]; exact Hsnap)
        (stepsOk_mono_le s s' _ Ht1 ⟨Hpv, Hsd⟩ Hc Ha Hpre Hstok) rfl (by rw [Hsg]; exact Hstor) (by rw [Hpre]; exact Hpvoff)
        (by rw [Hgh]; exact Hrs_out) (by rw [Hgh]; exact Hrs_unst) (Int.le_trans Hrs_clb Hc)
        $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstr'
    ipureintro
    rw [Htrm]
    exact ⟨Ht1, Ht2⟩)

end proof

end EtcdGrove
end Perennial

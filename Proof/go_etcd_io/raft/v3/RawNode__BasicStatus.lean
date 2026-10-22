/- Lean-first (no Rocq counterpart, 2026-10-13). -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__BasicStatus
public import Spec.go_etcd_io.raft.v3.getBasicStatus

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

/-- `getBasicStatus` on the raft struct; the bounds on `applied`/`committed` are the log's
(`ownRaftLog_ready_wf`) and `ownRawNode`'s (`Hdlen`, `Hrs_clb`). -/
theorem RawNode.BasicStatus.wp_proof
    (wp_getBasicStatus : getBasicStatus.spec (GF := GF) (hG := hG)) :
    RawNode.BasicStatus.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs
  wp_start as H
  iNamed H
  iNamed Hrn
  icases ownRaftPhysC_log_same cf rnv.raft' id s $$ Hphys with ⟨Hlog, Hback⟩
  icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hlwf, Hlog⟩
  ihave Hphys := Hback $$ Hlog
  wp_auto
  wp_apply wp_getBasicStatus cf rnv.raft' id s $$ Hphys as %hp ⟨#Hhs, Hphys⟩
  iapply HΦ $$ %_ %(hardstateVal (nodeHardstate s))
  simp only [named]
  isplitl
  · iapply ownRawNode_intro γ rn id rs s cf fp rnv sv hprev steps Hwf Hin Hal Hasync Hdlen Hunp Hsnap
      Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hloan
      $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hloanc
  simp only [basicStatusOf]
  iframe Hhs
  ipureintro
  obtain ⟨-, Hap1, Hap2⟩ := Hlwf
  have := uint_Z_nonneg s.logst.applying
  refine ⟨trivial, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [nodeHardstate, hardstateVal]) <;> (try rw [Htrm]) <;> omega

end proof

end EtcdGrove
end Perennial

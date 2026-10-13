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
  icases ownRaftPhys_log_same γ.reCfg rnv.raft' id s $$ Hphys with ⟨Hlog, Hback⟩
  icases ownRaftLog_ready_wf _ _ $$ Hlog with ⟨%Hwf, Hlog⟩
  ihave Hphys := Hback $$ Hlog
  wp_auto
  wp_apply wp_getBasicStatus γ.reCfg rnv.raft' id s $$ Hphys as Hphys
  iapply HΦ
  simp only [named]
  isplitl
  · iapply ownRawNode_intro γ rn id rs s ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap
      Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb
      $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs
  ipureintro
  obtain ⟨-, Hap1, Hap2⟩ := Hwf
  have := uint_Z_nonneg s.logst.applying
  refine ⟨rfl, Htrm.symm, ?_, ?_, Hrs_clb⟩ <;>
    simp only [basicStatusOf, nodeHardstate, hardstateVal] <;> omega

end proof

end EtcdGrove
end Perennial

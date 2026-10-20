/-
Proof of `Spec/go_etcd_io/raft/v3/tracker/ProgressTracker__ResetReplicationSet.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ResetReplicationSet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- With no witness (`ownCfgCC`'s `Witnesses = [0, 0]`) the early return: the fresh epoch of
subterm 0 and zero replication sets, made read-only, installed. -/
theorem tracker.ProgressTracker.ResetReplicationSet.wp_proof :
    tracker.ProgressTracker.ResetReplicationSet.spec (GF := GF) (hG := hG) := by
  intro c trk tv t
  wp_start as ⟨Htrk, Hown⟩
  iunfold ownTrackerC at Hown
  iNamed Hown
  icases ownCfgCC_elim _ _ _ $$ Hcfg with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal, %Hwit⟩
  wp_auto
  -- `p.Witnesses[0]` and `p.Witnesses[1]`, both `0`
  icases (Access.access
      (A := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Witnesses"] ↦
        tv.Config'.Witnesses')
      (A' := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Witnesses"] ↦
        tv.Config'.Witnesses')
      (P := trk ↦ tv)) $$ Htrk with ⟨Hwf, Htrkback⟩
  icases array_acc_same _ (sint.Z (W64 0)) _ _ _ (W64 0) (by decide) (by rw [Hwit]; rfl)
    $$ Hwf with ⟨Hw0, Hw0back⟩
  wp_auto
  ihave Hwf := Hw0back $$ Hw0
  icases array_acc_same _ (sint.Z (W64 1)) _ _ _ (W64 0) (by decide) (by rw [Hwit]; rfl)
    $$ Hwf with ⟨Hw1, Hw1back⟩
  wp_auto
  ihave Hwf := Hw1back $$ Hw1
  ihave Htrk := Htrkback $$ Hwf
  -- the new epoch, read-only from now on
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ «$r0» with #He
  wp_auto
  iapply HΦ
  iframe Htrk
  iapply ownTrackerC_intro c { tv with Epoch' := «$r0_ptr» } t.votes t.prs t.peers Hinv Hdom Hflags
    Hsize HmaxInfl Hnw
    $$ Hvotes Hprs Hprogs [Hin Hout Hl Hln] [He]
  · iapply ownCfgCC_intro _ _ c vin vout Harr Hal Hwit $$ Hin Hout Hl Hln
  · iunfold ownEpochNW
    iapply ownEpoch_bare_intro _ _ _ rfl rfl $$ He

end proof

end EtcdGrove
end Perennial

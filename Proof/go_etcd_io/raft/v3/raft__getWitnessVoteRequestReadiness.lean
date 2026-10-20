/-
`(*raft).getWitnessVoteRequestReadiness` on a witness-free configuration (2026-10-19, witness
support): both witnesses read `0`, so the function returns `nil` before it makes a map.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__getWitnessVoteRequestReadiness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

-- `w1 := r.trk.Witnesses[0]; w2 := r.trk.Witnesses[1]`, both `0`: `return nil`
set_option hygiene false in
local macro "gw_witnesses" : tactic => `(tactic| (
  icases (Access.access
      (A := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"].[tracker.Config,
        go!"Witnesses"] ↦ tv.Config'.Witnesses')
      (A' := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"].[tracker.Config,
        go!"Witnesses"] ↦ tv.Config'.Witnesses')
      (P := r.[raft, go!"trk"] ↦ tv)) $$ Htrkf with ⟨Hwf, Htrkback⟩
  icases array_acc_same _ (sint.Z (W64 0)) _ _ _ (W64 0) (by decide) (by rw [Hwit]; rfl)
    $$ Hwf with ⟨Hw0, Hw0back⟩
  wp_auto
  ihave Hwf := Hw0back $$ Hw0
  icases array_acc_same _ (sint.Z (W64 1)) _ _ _ (W64 0) (by decide) (by rw [Hwit]; rfl)
    $$ Hwf with ⟨Hw1, Hw1back⟩
  wp_auto
  ihave Hwf := Hw1back $$ Hw1
  ihave Htrkf := Htrkback $$ Hwf
  iapply HΦ
  iapply Hback $$ %tv Htrkf Htrk))

theorem raft.getWitnessVoteRequestReadiness.wp_proof :
    raft.getWitnessVoteRequestReadiness.spec (GF := GF) (hG := hG) := by
  intro c V r id s d v1 v2 Hd
  wp_start as Hphys
  -- STAGED: no witness yet (`ownRaftPhysC_wit0`)
  icases ownRaftPhysC_wit0 c r id s $$ Hphys with ⟨%hw, Hphys⟩
  icases ownRaftPhysC_tracker_same (c := c) (V := V) r id s $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTrackerC_witnesses $$ Htrk with ⟨%Hwit, Htrk⟩
  rw [hw] at Hwit
  wp_auto
  -- `v1 := votesToWin[0]; v2 := votesToWin[1]`
  icases array_acc_same _ (sint.Z (W64 0)) _ _ _ v1 (by decide) (by rw [Hd]; rfl)
    $$ votesToWin with ⟨Hv0, Hv0back⟩
  wp_auto
  ihave votesToWin := Hv0back $$ Hv0
  icases array_acc_same _ (sint.Z (W64 1)) _ _ _ v2 (by decide) (by rw [Hd]; rfl)
    $$ votesToWin with ⟨Hv1, Hv1back⟩
  wp_auto
  ihave votesToWin := Hv1back $$ Hv1
  -- `if v1 > 1 && v2 > 1 { return nil }`
  by_cases h1 : sint.Z (W64 1) < sint.Z v1
  · rw [decide_eq_true h1]
    wp_auto
    by_cases h2 : sint.Z (W64 1) < sint.Z v2
    · rw [decide_eq_true h2]
      wp_auto
      iapply HΦ
      iapply Hback $$ %tv Htrkf Htrk
    · rw [decide_eq_false h2]
      wp_auto
      gw_witnesses
  · rw [decide_eq_false h1]
    wp_auto
    gw_witnesses

end proof

end EtcdGrove
end Perennial

/-
Raft-side witness lemmas (2026-10-20, witness support, W3b-C): the configuration's witnesses
`r.trk.Witnesses` at any configuration (`[c.wit, 0]`, `ownTrackerC_witnesses`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The witness of half `i` of the configuration: `c.wit` for the incoming half, `0` for the
outgoing one (`ownTrackerC`'s `Witnesses = [c.wit, 0]`). -/
def witOf (c : CfgM) (i : w64) : w64 := if sint.Z i = 0 then c.wit else W64 0

/-- `r.trk.Witnesses[i]`, at any configuration: `witOf c i`. -/
theorem raft.wp_load_trk_witnessC' (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState)
    (i : w64) (hi : sint.Z i = 0 ∨ sint.Z i = 1) :
    {{ ownRaftPhysCV (GF := GF) c V r id s }}
      (App (Val (GoInstruction (GoLoad go.uint64)))
        (Val #(arrayIndexRef w64 (sint.Z i) ((r.[raft, go!"trk"]).[tracker.ProgressTracker,
          go!"Config"].[tracker.Config, go!"Witnesses"]))))
    {{ RET #(witOf c i); ownRaftPhysCV c V r id s }} := by
  iintro %Φ H HΦ
  icases ownRaftPhysC_tracker c r id s $$ H with ⟨%tv, Hf, Htrk, Hback⟩
  icases ownTrackerC_witnesses c tv _ $$ Htrk with ⟨%Hwit, Htrk⟩
  icases (Access.access
      (A := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"].[tracker.Config,
        go!"Witnesses"] ↦ tv.Config'.Witnesses')
      (A' := r.[raft, go!"trk"].[tracker.ProgressTracker, go!"Config"].[tracker.Config,
        go!"Witnesses"] ↦ tv.Config'.Witnesses')
      (P := r.[raft, go!"trk"] ↦ tv)) $$ Hf with ⟨Hwf, Hfback⟩
  icases array_acc_same _ (sint.Z i) _ _ _ (witOf c i) (by omega)
      (by rw [Hwit]; unfold witOf; rcases hi with h | h <;> rw [h] <;> rfl)
    $$ Hwf with ⟨Hw, Hwback⟩
  iapply IntoValTyped.wp_load (t := go.uint64) _ (DFrac.own 1) (witOf c i) $$ Hw
  inext
  iintro Hw
  ihave Hwf := Hwback $$ Hw
  ihave Hf := Hfback $$ Hwf
  iapply HΦ
  iapply Hback $$ %tv %s.votes Hf Htrk

theorem witOf_zero (c : CfgM) : witOf c (W64 0) = c.wit := by
  unfold witOf; simp

theorem witOf_one (c : CfgM) : witOf c (W64 1) = W64 0 := by
  unfold witOf; simp

/-- At a configuration with a witness the configuration is not joint (2026-10-20, W3b-C): the
static mode, where a configuration change leaves no witness (`ccApplyM_wit0`). STAGED: read out
of `witOwn`'s no-witness conjunct (`ownRaftPhysC_wit0`); the static-mode invariant that replaces
it must keep this. -/
theorem ownRaftPhysC_witSimple (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗
      ⌜c.wit ≠ W64 0 → c.outgoing = ∅⌝ ∗ ownRaftPhysCV c V r id s := by
  iintro H
  icases ownRaftPhysC_wit0 c _ _ _ $$ H with ⟨%hw, H⟩
  iframe H
  ipureintro
  exact fun h => absurd hw h

/-- The incoming half fits the tracker's bound. -/
theorem ownRaftPhysC_incoming_size (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState) :
    ⊢ ownRaftPhysCV (GF := GF) c V r id s -∗
      ⌜(GMap.size c.incoming : Int) ≤ 2 ^ 62⌝ ∗ ownRaftPhysCV c V r id s := by
  iintro H
  icases ownRaftPhysC_tracker c r id s $$ H with ⟨%tv, Hf, Htrk, Hback⟩
  icases ownTrackerC_voters_size c tv _ $$ Htrk with ⟨%Hsz, Htrk⟩
  ihave H := Hback $$ %tv %s.votes Hf Htrk
  iframe H
  ipureintro
  exact Hsz.2.1

end lemmas

end EtcdGrove
end Perennial

/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/HandleStep.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The run loop's ghost step for a proposal (`handleProposal`): through the node invariant
(`swift.run_upd`), one `sp.upd_handle`: the replica's sequence of its ballot gets `x`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The view after `x` is handled in the view's ballot. -/
def swift.LView.handled (w : swift.LView) (x : sp.CmdId) : swift.LView :=
  (w.1, w.2.1, w.2.2.1, (w.1, w.locAt w.1 ++ [x]) :: w.2.2.2)

theorem swift.LView.handled_locAt (w : swift.LView) (x : sp.CmdId) (b : Nat) :
    (w.handled x).locAt b = if b = w.1 then w.locAt w.1 ++ [x] else w.locAt b := by
  unfold swift.LView.handled swift.LView.locAt
  by_cases h : b = w.1
  · subst h; simp
  · simp [h, Ne.symm h]

/-- `localOk` after `handleProposal` handled `x` (normal operation). -/
theorem swift.localOk_handled (N r : Nat) (ld : Bool) (v v' : swift.RunV) (M : Option sp.SyncMsg)
    (w : swift.LView) (x : swift.CommandId) (gp : Loc) (hn : w.2.2.1 = true)
    (hok : swift.localOk N r ld v M w) (h1 : v'.ballot = v.ballot) (h2 : v'.cballot = v.cballot)
    (h3 : v'.status = v.status) (h4 : v'.handled = v.handled ++ [x])
    (h5 : v'.propsM = <[x := gp]> v.propsM) (hxn : toCmdId x ∉ w.locAt w.2.1) :
    swift.localOk N r ld v' M (w.handled (toCmdId x)) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13⟩ := hok
  have hbc : w.2.1 = w.1 := o6 hn
  refine ⟨by rw [h1]; exact o1, by rw [h2]; exact o2, by rw [h1]; exact o3, by rw [h2]; exact o4,
    by rw [h3]; exact o5, fun _ => o6 hn, o7, ?_, ?_, ?_, o11, ?_, ?_⟩
  · show (w.handled (toCmdId x)).locAt w.2.1 = _
    rw [swift.LView.handled_locAt, if_pos hbc, ← hbc, o8, h4]; simp
  · intro y hy
    change y ∈ (w.handled (toCmdId x)).locAt w.2.1 at hy
    rw [swift.LView.handled_locAt, if_pos hbc, ← hbc] at hy
    rw [h5]
    rcases List.mem_append.mp hy with hy | hy
    · have := o9 y hy
      by_cases e : ofCmdId y = x
      · rw [e, GMap.lookup_insert]; rfl
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; exact this
    · simp at hy; subst hy
      have : ofCmdId (toCmdId x) = x := by cases x; rfl
      rw [this, GMap.lookup_insert]; rfl
  · intro b o hb hmem
    have hb' : w.2.1 < b := hb
    change (b, o) ∈ (w.1, w.locAt w.1 ++ [toCmdId x]) :: w.2.2.2 at hmem
    rcases List.mem_cons.mp hmem with e | e
    · have := congrArg Prod.fst e; simp only at this; omega
    · exact o10 b o hb' e
  · show ((w.handled (toCmdId x)).locAt w.2.1).Nodup
    rw [swift.LView.handled_locAt, if_pos hbc, ← hbc]
    exact List.nodup_append.mpr ⟨o12, by simp, fun a ha b hb => by
      simp at hb; subst hb; intro e; subst e; exact hxn ha⟩
  · intro y hy
    show y ∈ (w.handled (toCmdId x)).locAt w.2.1
    rw [swift.LView.handled_locAt, if_pos hbc, ← hbc]
    rw [h5] at hy
    by_cases e : ofCmdId y = x
    · apply List.mem_append_right; subst e; rw [toCmdId_ofCmdId]; exact List.mem_singleton_self _
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hy
      exact List.mem_append_left _ (o13 y hy)

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS] [Perennial.github_com.imdea_software.swiftpaxos.sp.GobFmt]

/-- The base of the run loop's `cballot` from its last `MSync`. -/
theorem swift.syncObj_base (γ : sp.Names) (N : Nat) (ls : Loc) (b : Nat)
    (M : Option sp.SyncMsg) (hM : M = none ↔ b = 0) :
    swift.syncObj γ N ls b M ⊢
      iprop(⌜b = 0 ∧ (M.map sp.syncOrder).getD [] = []⌝ ∨
        ∃ M0, sp.syncIs γ b M0 ∗ ⌜(M.map sp.syncOrder).getD [] = sp.syncOrder M0⌝) := by
  cases M with
  | none =>
    iintro _; ileft; ipureintro; exact ⟨hM.1 rfl, rfl⟩
  | some M0 =>
    iintro H
    unfold swift.syncObj
    icases H with ⟨%ph, %cm, %dp, %rep, %bl, -, -, #Hs, -, -⟩
    iright; iexists M0; iframe Hs; ipureintro; rfl

end lemmas

end Perennial.github_com.imdea_software.swiftpaxos

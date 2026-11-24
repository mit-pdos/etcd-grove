/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/IntfStep.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AI, internal: **preservation of the interference invariant** by one step (`intf_step`), given
the agreement invariant before and after the step (ids, ballots, instances below their owner's
`crt`), and along runs (`intf_run`).
-/
module

public import Dsverify.Proof.gryff.PureA.IntfQuiet

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AI

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA
open Perennial.gryff.pureA.AW

/-- A step's obligations give the invariant after it (no creation). -/
theorem post_of_stepI {c c1 : Cfg gNet} {G' : GG} {κ : Nat} {rc : RecG} {dg : DepG} {a : Fin 3}
    {e : Ev} {s' : RState} {o : List Out} {ox : Option (w32 × w32)}
    (I : CInv c G) (I1 : CInv c1 G') (J : IInv c κ rc dg) (hp : Post c a e s' o c1) (hloc : Loc s')
    (hcrt : ∀ r, sint.Z ((c.st r).crt (rid32 r)) ≤ sint.Z ((c1.st r).crt (rid32 r)))
    (S : StepI rc κ dg (c.st a) s' a o ox) : IInv c1 (κ + 1) (addRec rc a κ ox) dg := by
  have hid := I.ids a
  refine intf_post J hp hloc (DgLe.refl dg) (fun _ _ _ h => Or.inl h) S.conf ?_ hcrt ?_ S.loc
  · intro q j hx
    obtain ⟨k1, k2, k3⟩ := S.recd q j hx
    refine ⟨k1, ?_, ?_⟩
    · obtain ⟨cp, hcp⟩ := Option.ne_none_iff_exists'.1 k2
      have hc1 : cpOf c1 a q j = some cp := by unfold cpOf; rw [st_postA hp]; exact hcp
      obtain ⟨hrow, -, hlt⟩ := I1.copyBelow a q j cp hc1
      exact ⟨rowOf q, (rid32_rowOf hrow).symm, by rw [rid32_rowOf hrow]; exact hlt⟩
    · rcases k3 with e | e
      · exact Or.inl (e.trans hid)
      · exact Or.inr e
  · intro j h0 hlt
    have e1 := S.crtOwn
    rw [hid] at e1
    rw [e1] at hlt
    obtain ⟨t, ht⟩ := J.ownRow a j h0 hlt
    exact ⟨t, (addRec_ext rc a κ ox).keep _ _ _ _ ht⟩

/-- **The interference invariant after a step.** -/
theorem intf_step {c c1 : Cfg gNet} {G G' : GG} {κ : Nat} {rc : RecG} {dg : DepG} {a : Fin 3}
    {e : Ev} {x : List Ext} (I : CInv c G) (I1 : CInv c1 G') (J : IInv c κ rc dg)
    (h : GStep c a e c1 x) : ∃ rc' dg', IInv c1 (κ + 1) rc' dg' := by
  obtain ⟨s', o, hs, hrecv, -, hst, hinf⟩ := h
  have hp : Post c a e s' o c1 := ⟨hst, hinf⟩
  have hok := gstep_ok hs
  have hm : ∀ m, e = .msg m → m ∈ c.inflight a := fun m he => hrecv m (by subst he; rfl)
  have hid := I.ids a
  have C : CtxI rc κ dg (c.st a) a :=
    ⟨hid, fun q i cp h => J.copies a q i cp h, J.tab a, J.confLen a, J.clock, J.own⟩
  have hlk := step_lk (J.loc a) hok
  have hloc := loc_of_lstep (J.loc a) hlk.1
  have hcrt : ∀ r : Fin 3, sint.Z ((c.st r).crt (rid32 r)) ≤ sint.Z ((c1.st r).crt (rid32 r)) := by
    intro r
    by_cases hr : r = a
    · subst hr; rw [st_postA hp]
      have k := hlk.1.2.2.1; rw [hid] at k; exact k
    · rw [st_postN hp hr]; exact Int.le_refl _
  have gen : ∀ ox, StepI rc κ dg (c.st a) s' a o ox → ∃ rc' dg', IInv c1 (κ + 1) rc' dg' :=
    fun ox S => ⟨_, _, post_of_stepI I I1 J hp hloc hcrt S⟩
  have hW : ∀ m, e = .msg m → MsgI rc κ dg a m := fun m he => J.msgs a m (hm m he)
  -- an instance a message names is below its owner's `crt`
  have below : ∀ m q j, e = .msg m → msgInst m = some (q, j) → q = (c.st a).id →
      sint.Z j < sint.Z ((c.st a).crt q) := fun m q j he hmi hq => by
    obtain ⟨-, -, hlt⟩ := I.msgBelow a m q j (hm m he) hmi
    rw [hq, hid, rowOf_rid32] at hlt; rw [hq, hid]; exact hlt
  cases e with
  | read => exact gen _ (stepI_frame (stepClientRead_frame hok) (stepClientRead_conf hok)
      (stepClientRead_quiet hok))
  | write => exact gen _ (stepI_frame (stepClientWrite_frame hok) (stepClientWrite_conf hok)
      (stepClientWrite_quiet hok))
  | forceWrite => cases hok; exact gen _ (stepI_frame ⟨rfl, rfl, rfl⟩ rfl quietO_nil)
  | recover q i =>
    exact gen _ (li_recover C (fun cp hc => ((I.inst q i).copies a cp hc).nonneg) hok)
  | exec => exact gen _ (stepI_sim C (stepExec_sim hok).1 (stepExec_conf hok) (stepExec_sim hok).2)
  | rmw rid cid k d oldV newV =>
    obtain ⟨D, hconf, hcv, hcp, hown', hL⟩ := li_rmw C (I.crtLen a) (J.ownRow a) hok
    have i0 := (c.st a).crt (rid32 a)
    have fresh : dg (rid32 a) ((c.st a).crt (rid32 a)) = none := by
      cases hx : dg (rid32 a) ((c.st a).crt (rid32 a)) with
      | none => rfl
      | some D' =>
        obtain ⟨r, t, hr, ht⟩ := J.dgRec _ _ _ hx
        obtain ⟨r', hr', hlt⟩ := J.born _ _ _ _ ht
        have := rid32_inj hr'; subst this
        exact absurd hlt (Int.lt_irrefl _)
    refine ⟨_, _, intf_post J hp hloc (dgSet_le fresh) ?_ hconf ?_ hcrt ?_ hL⟩
    · intro q j D' hD'
      unfold dgSet at hD'
      split at hD'
      · rename_i e; obtain ⟨rfl, rfl⟩ := e
        right
        obtain ⟨t, ht, -⟩ := addRec_self (rc := rc) (a := a) (κ := κ) (q := rid32 a)
          (j := (c.st a).crt (rid32 a)) (fun t ht => J.clock _ _ _ _ ht)
        exact ⟨a, t, rfl, ht⟩
      · exact Or.inl hD'
    · intro q j hx
      cases hx
      refine ⟨hcv, ?_, Or.inl rfl⟩
      obtain ⟨cp, hcp'⟩ := Option.ne_none_iff_exists'.1 hcp
      have hc1 : cpOf c1 a (rid32 a) ((c.st a).crt (rid32 a)) = some cp := by
        unfold cpOf; rw [st_postA hp]; exact hcp'
      obtain ⟨hrow, -, hlt⟩ := I1.copyBelow a _ _ cp hc1
      rw [rowOf_rid32] at hlt
      exact ⟨a, rfl, hlt⟩
    · intro j h0 hlt
      rcases hown' j h0 hlt with hlt' | rfl
      · obtain ⟨t, ht⟩ := J.ownRow a j h0 hlt'
        exact ⟨t, (addRec_ext rc a κ _).keep _ _ _ _ ht⟩
      · obtain ⟨t, ht, -⟩ := addRec_self (rc := rc) (a := a) (κ := κ) (q := rid32 a)
          (j := (c.st a).crt (rid32 a)) (fun t ht => J.clock _ _ _ _ ht)
        exact ⟨t, ht⟩
  | msg m =>
    cases m with
    | read1 => exact gen _ (stepI_frame (stepRead1_frame hok) (stepRead1_conf hok)
        (stepRead1_quiet hok))
    | read2 => exact gen _ (stepI_frame (stepRead2_frame hok) (stepRead2_conf hok)
        (stepRead2_quiet hok))
    | write1 => exact gen _ (stepI_frame (stepWrite1_frame hok) (stepWrite1_conf hok)
        (stepWrite1_quiet hok))
    | write2 => exact gen _ (stepI_frame (stepWrite2_frame hok) (stepWrite2_conf hok)
        (stepWrite2_quiet hok))
    | read1Reply => exact gen _ (stepI_frame (stepRead1Reply_frame hok) (stepRead1Reply_conf hok)
        (stepRead1Reply_quiet hok))
    | read2Reply => exact gen _ (stepI_frame (stepRead2Reply_frame hok) (stepRead2Reply_conf hok)
        (stepRead2Reply_quiet hok))
    | write1Reply => exact gen _ (stepI_frame (stepWrite1Reply_frame hok)
        (stepWrite1Reply_conf hok) (stepWrite1Reply_quiet hok))
    | write2Reply => exact gen _ (stepI_frame (stepWrite2Reply_frame hok)
        (stepWrite2Reply_conf hok) (stepWrite2Reply_quiet hok))
    | prepare m =>
      have k := I.msgs a _ (hm _ rfl)
      exact gen _ (li_prepare C (fun e => by have := k.1; rw [e] at this; exact absurd this (by decide)) hok)
    | preAccept m =>
      have k := I.msgs a _ (hm _ rfl)
      refine gen _ (Classical.choose_spec (li_preAccept C (hW _ rfl) (fun hi => ?_) (fun h0 e => ?_)
        (below _ _ _ rfl rfl) hok))
      · by_cases hne : m.ballot = 0
        · exact hne
        exfalso
        obtain ⟨-, -, R, hR, -⟩ := k.2 hne
        have := SPA.own_ge hR; have := SPA.init_lt hi; omega
      · obtain ⟨hd, -⟩ := k.1 h0
        exact hd (by rw [e, rowOf_rid32])
    | accept m => exact gen _ (li_accept C (hW _ rfl) (below _ _ _ rfl rfl) hok)
    | commit m => exact gen _ (li_commit C (hW _ rfl) (below _ _ _ rfl rfl) hok)
    | prepareReply m =>
      have k := I.msgs a _ (hm _ rfl)
      refine gen _ (Classical.choose_spec (li_prepareReply C (hW _ rfl) (fun hne e0 => ?_) hok))
      rcases k.2.2 with ht | hf
      · obtain ⟨-, Y, -, -, hown, -⟩ := k.2.1 ht
        have := pureA.own_pos hown
        rw [e0] at this; exact absurd this (by decide)
      · exact hne hf
    | preAcceptReply => exact gen _ (li_preAcceptReply C (hW _ rfl) hok)
    | preAcceptOK m =>
      refine gen _ (li_preAcceptOK C (hW _ rfl) (fun cp hc hi => ?_) hok)
      rw [hid] at hc
      rcases ((I.inst _ _).copies a cp hc).ballotForm with e | ⟨R, hR⟩
      · exact e
      · have := SPA.own_ge hR; have := SPA.init_lt hi; omega
    | acceptReply => exact gen _ (li_acceptReply C hok)
    | executed =>
      exact gen _ (stepI_sim C (handleExecuted_sim hok).1 (handleExecuted_conf hok)
        (handleExecuted_sim hok).2)
    | executeOverwrite =>
      exact gen _ (stepI_sim C (stepExecuteOverwrite_sim hok).1 (stepExecuteOverwrite_conf hok)
        (stepExecuteOverwrite_sim hok).2)

/-- The invariant along a run. -/
theorem intf_run {c c' : Cfg gNet} {G : GG} {κ : Nat} {rc : RecG} {dg : DepG} {l : List Label}
    (I : CInv c G) (J : IInv c κ rc dg) (h : GRun c l c') : ∃ κ' rc' dg', IInv c' κ' rc' dg' := by
  induction h generalizing G κ rc dg with
  | nil c => exact ⟨_, _, _, J⟩
  | cons hs _ ih =>
    obtain ⟨G1, I1, -⟩ := inv_step I hs
    obtain ⟨rc1, dg1, J1⟩ := intf_step I I1 J hs
    exact ih I1 J1

end Perennial.gryff.pureA.AI

/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureA/WitStep.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit AW, internal: **preservation of the witness invariant** by one step (`wit_step`), given the
agreement invariant before and after the step and the stores' growth. The ghost changes only at an
RMW (`newS`: the new instance `(id, crt[id])` gets the current stores).
-/
module

public import Dsverify.Proof.gryff.PureA.WitSteps

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pureA.AW

open Perennial Perennial.gryff.model Perennial.gryff.pure Perennial.gryff.kahn Perennial.gryff.pureA

/-- The ghost after a step of replica `a` from `c`: an RMW records the stores at its instance. -/
def newS (c : Cfg gNet) (a : Fin 3) (e : Ev) (S : CSG) : CSG :=
  match e with
  | .rmw .. => S.set (rid32 a) ((c.st a).crt (rid32 a)) (fun w => (c.st w).tag)
  | _ => S

theorem newS_rmw (c : Cfg gNet) (a : Fin 3) (S : CSG) {rid cid : w32} {k : w64} {d : Dep}
    {oldV newV : w64} : newS c a (.rmw rid cid k d oldV newV) S =
      S.set (rid32 a) ((c.st a).crt (rid32 a)) (fun w => (c.st w).tag) := rfl

/-- The new instance is not in the ghost yet. -/
theorem fresh_slot {c : Cfg gNet} {S : CSG} (W : WInv c S) (a : Fin 3) :
    S (rid32 a) ((c.st a).crt (rid32 a)) = none := by
  cases hx : S (rid32 a) ((c.st a).crt (rid32 a)) with
  | none => rfl
  | some f =>
    obtain ⟨r, hr, hlt⟩ := W.born _ _ _ hx
    have := rid32_inj hr; subst this
    exact absurd hlt (Int.lt_irrefl _)

theorem newS_le {c : Cfg gNet} {S : CSG} (W : WInv c S) (a : Fin 3) (e : Ev) :
    SLe S (newS c a e S) := by
  cases e <;> first | exact SLe.refl S | exact CSG.set_le (fresh_slot W a)

/-- **The witness invariant after a step.** -/
theorem wit_step {c c1 : Cfg gNet} {G G' : GG} {S : CSG} {a : Fin 3} {e : Ev} {x : List Ext}
    (I : CInv c G) (I1 : CInv c1 G') (W : WInv c S) (h : GStep c a e c1 x)
    (hmono : ∀ w : Fin 3, TLe (c.st w).tag (c1.st w).tag) : WInv c1 (newS c a e S) := by
  obtain ⟨s', o, hs, hrecv, -, hst, hinf⟩ := h
  have hp : Post c a e s' o c1 := ⟨hst, hinf⟩
  have hok := gstep_ok hs
  have hm : ∀ m, e = .msg m → m ∈ c.inflight a := fun m he => hrecv m (by subst he; rfl)
  have C : Ctx S (c.st a) a :=
    ⟨I.ids a, fun q i cp h => W.copies a q i cp h, fun q i f h => W.store q i f h a⟩
  have hlk := step_lk (W.loc a) hok
  have hloc := loc_of_lstep (W.loc a) hlk.1
  have hcrt : ∀ r : Fin 3, sint.Z ((c.st r).crt (rid32 r)) ≤ sint.Z ((c1.st r).crt (rid32 r)) := by
    intro r
    by_cases hr : r = a
    · subst hr; rw [st_postA hp]
      have k := hlk.1.2.2.1; rw [I.ids r] at k; exact k
    · rw [st_postN hp hr]; exact Int.le_refl _
  have born_old : ∀ q i f, S q i = some f → ∃ r : Fin 3, q = rid32 r ∧
      sint.Z i < sint.Z ((c1.st r).crt (rid32 r)) := fun q i f hf => by
    obtain ⟨r, hr, hlt⟩ := W.born q i f hf
    exact ⟨r, hr, Int.lt_of_lt_of_le hlt (hcrt r)⟩
  have store_old : ∀ q i f, S q i = some f → ∀ w, TLe (f w) (c1.st w).tag := fun q i f hf w =>
    TLe.trans (W.store q i f hf w) (hmono w)
  have gen : LocalW S (c.st a) s' a o → WInv c1 S := fun hL =>
    wit_post W hp (SLe.refl S) hloc store_old born_old hL
  have hW : ∀ m, e = .msg m → WMsg S a m := fun m he => W.msgs a m (hm m he)
  cases e with
  | read => exact gen (localW_frame (stepClientRead_frame hok) (stepClientRead_quiet hok))
  | write => exact gen (localW_frame (stepClientWrite_frame hok) (stepClientWrite_quiet hok))
  | forceWrite => cases hok; exact gen (localW_frame ⟨rfl, rfl, rfl⟩ quietO_nil)
  | recover => exact gen (lw_recover C hok)
  | exec =>
    have k := stepExec_sim hok
    exact gen (localW_sim C.copies k.1 k.2)
  | rmw rid cid k d oldV newV =>
    rw [newS_rmw]
    have hS := fresh_slot W a
    have hL := lw_rmw (F := fun w => (c.st w).tag) C rfl hS hok
    refine wit_post W hp (CSG.set_le hS) hloc ?_ ?_ hL
    · intro q i f hf
      unfold CSG.set at hf
      split at hf
      · cases hf; exact hmono
      · exact store_old q i f hf
    · intro q i f hf
      unfold CSG.set at hf
      split at hf
      · rename_i e; obtain ⟨rfl, rfl⟩ := e
        obtain ⟨c', -, -, hi, -⟩ := rmw_facts hok
        have hc1 : cpOf c1 a (rid32 a) ((c.st a).crt (rid32 a)) = some c' := by
          unfold cpOf; rw [st_postA hp, hi, if_pos ⟨(I.ids a).symm, by rw [I.ids a]⟩]
        obtain ⟨-, -, hlt⟩ := I1.copyBelow a _ _ c' hc1
        rw [rowOf_rid32] at hlt
        exact ⟨a, rfl, hlt⟩
      · exact born_old q i f hf
  | msg m =>
    cases m with
    | read1 => exact gen (localW_frame (stepRead1_frame hok) (stepRead1_quiet hok))
    | read2 => exact gen (localW_frame (stepRead2_frame hok) (stepRead2_quiet hok))
    | write1 => exact gen (localW_frame (stepWrite1_frame hok) (stepWrite1_quiet hok))
    | write2 => exact gen (localW_frame (stepWrite2_frame hok) (stepWrite2_quiet hok))
    | read1Reply => exact gen (localW_frame (stepRead1Reply_frame hok) (stepRead1Reply_quiet hok))
    | read2Reply => exact gen (localW_frame (stepRead2Reply_frame hok) (stepRead2Reply_quiet hok))
    | write1Reply =>
      exact gen (localW_frame (stepWrite1Reply_frame hok) (stepWrite1Reply_quiet hok))
    | write2Reply =>
      exact gen (localW_frame (stepWrite2Reply_frame hok) (stepWrite2Reply_quiet hok))
    | prepare => exact gen (lw_prepare C hok)
    | preAccept m =>
      have k := I.msgs a _ (hm _ rfl)
      refine gen (lw_preAccept C (hW _ rfl) (fun hi => ?_) hok)
      by_cases hne : m.ballot = 0
      · exact hne
      exfalso
      obtain ⟨-, -, R, hR, -⟩ := k.2 hne
      have := SPA.own_ge hR; have := SPA.init_lt hi; omega
    | accept => exact gen (lw_accept C (hW _ rfl) hok)
    | commit => exact gen (lw_commit (hW _ rfl) hok)
    | prepareReply m =>
      have k := I.msgs a _ (hm _ rfl)
      refine gen (lw_prepareReply C (hW _ rfl) (fun hne e0 => ?_) hok)
      rcases k.2.2 with ht | hf
      · obtain ⟨-, Y, -, -, hown, -⟩ := k.2.1 ht
        have := own_pos hown
        rw [e0] at this; exact absurd this (by decide)
      · exact hne hf
    | preAcceptReply => exact gen (lw_preAcceptReply C (hW _ rfl) hok)
    | preAcceptOK => exact gen (lw_preAcceptOK C (hW _ rfl) hok)
    | acceptReply => exact gen (lw_acceptReply C hok)
    | executed =>
      have k := handleExecuted_sim hok
      exact gen (localW_sim C.copies k.1 k.2)
    | executeOverwrite =>
      have k := stepExecuteOverwrite_sim hok
      exact gen (localW_sim C.copies k.1 k.2)

end Perennial.gryff.pureA.AW

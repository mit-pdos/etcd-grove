/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLa/Post.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-a: a step's effect on the tag bound (`step_post`): the bounds grow by the replica's
potential (`Pot`) and its executions with a result (`dEx`).
-/
module

public import Dsverify.Proof.gryff.PureLa.Steps2
public import Dsverify.Proof.gryff.PureLa.ExecCount

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.La

open model kahn Perennial.gryff.pure

/-- What a step keeps: new bounds `T' ∈ [T, T + ΔPot]`, `E + dEx`. -/
def Post (T E : Int) (e : Ev) (s s' : RState) (o : List Out) : Prop :=
  ∃ T', T ≤ T' ∧ T' - T ≤ Pot s' - Pot s ∧ SB T' (E + (dEx e o : Int)) s' ∧
    OB T' (E + (dEx e o : Int)) o ∧ Srt s'.wops ∧ s'.nReqs ≤ 24

theorem post_neutral {T E : Int} {e : Ev} {s s' : RState} {o : List Out} (hsrt : Srt s.wops)
    (hn : s.nReqs ≤ 24) (h : SB T E s' ∧ OB T E o) (hw : s'.wops = s.wops)
    (hnr : s'.nReqs = s.nReqs) (hd : dEx e o = 0) : Post T E e s s' o := by
  refine ⟨T, Int.le_refl _, ?_, ?_, ?_, hw ▸ hsrt, hnr ▸ hn⟩
  · unfold Pot; rw [hw, hnr]; omega
  · rw [hd]; simpa using h.1
  · rw [hd]; simpa using h.2

theorem post_of {T E : Int} {e : Ev} {s s' : RState} {o : List Out} (hd : dEx e o = 0)
    (h : ∃ T', T ≤ T' ∧ T' - T ≤ Pot s' - Pot s ∧ SB T' E s' ∧ OB T' E o ∧ Srt s'.wops ∧
      s'.nReqs ≤ 24) : Post T E e s s' o := by
  obtain ⟨T', h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨T', h1, h2, ?_, ?_, h5, h6⟩
  · rw [hd]; simpa using h3
  · rw [hd]; simpa using h4

theorem post_of' {T E : Int} {e : Ev} {s s' : RState} {o : List Out} (hd : dEx e o = 0)
    (hn : s.nReqs ≤ 24) (h : ∃ T', T ≤ T' ∧ T' - T ≤ Pot s' - Pot s ∧ SB T' E s' ∧ OB T' E o ∧
      Srt s'.wops ∧ s'.nReqs = s.nReqs) : Post T E e s s' o := by
  obtain ⟨T', h1, h2, h3, h4, h5, h6⟩ := h
  exact post_of hd ⟨T', h1, h2, h3, h4, h5, h6 ▸ hn⟩

theorem fw_wops {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) (he : Ev.wspecial e = false) : s'.wops = s.wops :=
  (step_fw_other h he).1.1

theorem step_post {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out} {T E : Int}
    (hs : SB T E s) (hm : ∀ m, e.recv = some m → MB T E m) (hsrt : Srt s.wops)
    (hn : s.nReqs ≤ 24) (hT : 0 ≤ T) (hT72 : T ≤ 72) (hE : 0 ≤ E) (hE2 : E < 2 ^ 31 - 2)
    (h : stepR r s e = .ok (s', o)) : Post T E e s s' o := by
  have hnr : isReqEv e = false → s'.nReqs = s.nReqs := step_nReqs h
  have hfw : Ev.wspecial e = false → s'.wops = s.wops := fw_wops h
  cases e with
  | read => exact post_of rfl (stepClientRead_tb hs hT hE hT72 hsrt hn h)
  | write => exact post_of rfl (stepClientWrite_tb hs hT hE hT72 hsrt hn h)
  | rmw => exact post_of rfl (stepClientRMW_tb hs hT hE hT72 hsrt hn h)
  | forceWrite => cases h; exact post_neutral hsrt hn ⟨hs, OB_nil⟩ rfl rfl rfl
  | recover => exact post_neutral hsrt hn (stepRecover_tb hs hT hE h) (hfw rfl) (hnr rfl) rfl
  | exec q i =>
    have := stepExec_tb hs hT hE hT72 hsrt hE2 h
    refine ⟨T, Int.le_refl _, ?_, ?_, ?_, hfw rfl ▸ hsrt, hnr rfl ▸ hn⟩
    · unfold Pot; rw [hfw rfl, hnr rfl]; omega
    · have e : ((dEx (.exec q i) o : Nat) : Int) = if (execRes o).isSome then 1 else 0 := by
        simp only [dEx]; split <;> simp
      rw [e]; exact this.1
    · have e : ((dEx (.exec q i) o : Nat) : Int) = if (execRes o).isSome then 1 else 0 := by
        simp only [dEx]; split <;> simp
      rw [e]; exact this.2
  | msg m =>
    have hm' := hm m rfl
    cases m with
    | read1 => exact post_neutral hsrt hn (stepRead1_tb hs hT hE hm' h) (hfw rfl) (hnr rfl) rfl
    | read2 => exact post_neutral hsrt hn (stepRead2_tb hs hT hE hm' h) (hfw rfl) (hnr rfl) rfl
    | write1 =>
      exact post_neutral hsrt hn (stepWrite1_tb hs hT hE hm' h) (stepWrite1_spec h).1.1 (hnr rfl) rfl
    | write2 => exact post_neutral hsrt hn (stepWrite2_tb hs hT hE hm' h) (hfw rfl) (hnr rfl) rfl
    | read1Reply =>
      exact post_neutral hsrt hn (stepRead1Reply_tb hs hT hE hm' h) (hfw rfl) (hnr rfl) rfl
    | read2Reply =>
      exact post_neutral hsrt hn (stepRead2Reply_tb hs hT hE h) (hfw rfl) (hnr rfl) rfl
    | write1Reply => exact post_of' rfl hn (stepWrite1Reply_tb hs hT hE hT72 hsrt hm' h)
    | write2Reply => exact post_of' rfl hn (stepWrite2Reply_tb hs hT hE hT72 hsrt h)
    | prepare => exact post_neutral hsrt hn (stepPrepare_tb hs hT hE h) (hfw rfl) (hnr rfl) rfl
    | preAccept =>
      exact post_neutral hsrt hn (stepPreAccept_tb hs hT hE hm' h) (hfw rfl) (hnr rfl) rfl
    | accept => exact post_neutral hsrt hn (stepAccept_tb hs hT hE hm' h) (hfw rfl) (hnr rfl) rfl
    | commit => exact post_neutral hsrt hn (stepCommit_tb hs hT hE hm' h) (hfw rfl) (hnr rfl) rfl
    | prepareReply =>
      exact post_neutral hsrt hn (stepPrepareReply_tb hs hT hE hm' h) (hfw rfl) (hnr rfl) rfl
    | preAcceptReply =>
      exact post_neutral hsrt hn (stepPreAcceptReply_tb hs hT hE hm' h) (hfw rfl) (hnr rfl) rfl
    | preAcceptOK =>
      exact post_neutral hsrt hn (stepPreAcceptOK_tb hs hT hE h) (hfw rfl) (hnr rfl) rfl
    | acceptReply =>
      exact post_neutral hsrt hn (stepAcceptReply_tb hs hT hE h) (hfw rfl) (hnr rfl) rfl
    | executed => exact post_neutral hsrt hn (handleExecuted_tb hs hT hE h) (hfw rfl) (hnr rfl) rfl
    | executeOverwrite =>
      exact post_neutral hsrt hn (stepExecuteOverwrite_tb hs hT hE hm' h) (hfw rfl) (hnr rfl) rfl

end Perennial.gryff.pure.La

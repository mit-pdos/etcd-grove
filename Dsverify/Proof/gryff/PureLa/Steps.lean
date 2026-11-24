/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLa/Steps.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-a: the tag bound kept by each handler (`*_tb`): a lemma per handler, by peeling its `do`
block (`PureL/Peel.lean`), as `PureL/StoreSteps.lean`.
-/
module

public import Dsverify.Proof.gryff.PureLa.Defs

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.La

open model kahn Perennial.gryff.pure

theorem TB_of_inst {T E : Int} {s : RState} (hs : SB T E s) {q i : w32} {c : Copy}
    (hc : s.inst q i = some c) : TB T E c.base.t := (hs.inst q i c hc).1

theorem TB_of_ri {T E : Int} {s : RState} (hs : SB T E s) {q i : w32} {c : Copy} {lb : LB}
    {ri : RecoveryInstance} (hc : s.inst q i = some c) (hl : c.lb = some lb)
    (hr : lb.recoveryInst = some ri) : TB T E ri.base.t := (hs.inst q i c hc).2 lb hl ri hr

theorem TB_ow {T E : Int} {s : RState} {v : w64} {t : model.Tag} (h1 : TB T E s.tag)
    (h2 : TB T E t) : TB T E (s.overwrite v t).tag := by
  unfold RState.overwrite; split
  · exact h2
  · exact h1

theorem TB_of_ri' {T E : Int} {s : RState} {q i : w32} {c : Copy} {lb : LB}
    {ri : RecoveryInstance} (hr : lb.recoveryInst = some ri) (hl : c.lb = some lb)
    (hc : s.inst q i = some c) (hs : SB T E s) : TB T E ri.base.t := (hs.inst q i c hc).2 lb hl ri hr

theorem TB_store {T E : Int} {s : RState} (hs : SB T E s) : TB T E s.storeVT.t := hs.tag

syntax "tb" : tactic
macro_rules
  | `(tactic| tb) => `(tactic| (
    try dsimp only [RState.setCrt, RState.setInst, RState.storeVT, riOf, vt0]
    first
    | with_reducible exact TB_tag0 ‹_› ‹_›
    | with_reducible exact ‹SB _ _ _›.tag
    | with_reducible assumption
    | exact TB_of_inst ‹SB _ _ _› (by assumption)
    | exact TB_of_ri' (by assumption) (by assumption) (by assumption) ‹SB _ _ _›
    | ((with_reducible apply TB_ow) <;> tb)
    | (split <;> tb)))

syntax "cb" : tactic
macro_rules
  | `(tactic| cb) => `(tactic| first | with_reducible assumption | (
    refine ⟨?_, fun lb hl ri hr => ?_⟩
    · tb
    · try dsimp only at hl
      first
      | (cases hl; done)
      | exact TB_of_ri ‹SB _ _ _› (by assumption) hl hr
      | (cases hl; (try dsimp only at hr); first
          | (cases hr; done)
          | exact TB_of_ri ‹SB _ _ _› (by assumption) (by assumption) hr
          | (cases hr; dsimp only [riOf]; tb))))

set_option hygiene false in
syntax "sb" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sb) => `(tactic| first
    | with_reducible assumption
    | ((with_reducible apply SB.updateConflicts); sb)
    | ((with_reducible apply SB.setCrt); sb)
    | ((with_reducible apply SB.setInst) <;> first | sb | cb)
    | ((with_reducible apply SB.overwrite) <;> first | sb | tb)
    | exact SB.of_eq hs rfl rfl rfl rfl rfl
    | exact SB.of_eq hsb rfl rfl rfl rfl rfl)

syntax "mb" : tactic
macro_rules
  | `(tactic| mb) => `(tactic| (simp only [MB] <;> first | tb | (refine ⟨?_, ?_⟩ <;> tb) | assumption))

syntax "ob" : tactic
macro_rules
  | `(tactic| ob) => `(tactic| first
    | exact OB_nil
    | exact OB_ext
    | ((with_reducible apply OB_append) <;> ob)
    | ((with_reducible apply OB_sendPeer ‹sendPeer _ _ _ = some _›); mb)
    | ((with_reducible apply OB_sendTo ‹sendTo _ _ = some _›); mb)
    | ((with_reducible apply OB_mapM_sendTo ‹_›); mb)
    | ((with_reducible apply OB_mapM_sendPeer ‹_›); mb)
    | ((with_reducible apply OB_bcast ‹bcast _ _ = some _›); mb)
    | (apply OB_bcast ‹bcastPreAccept _ _ _ _ _ _ _ _ = some _›; mb)
    | (apply OB_bcast ‹bcastAccept _ _ _ _ _ _ _ _ = some _›; mb)
    | (apply OB_bcast ‹bcastCommit _ _ _ _ _ _ _ = some _›; mb)
    | (apply OB_bcast ‹bcastPrepare _ _ _ _ = some _›; mb))

set_option hygiene false in
macro "tb_fin" : tactic => `(tactic| (
  try (have hu := ‹updateCommitted _ _ = some _›; have hsb := SB.updateCommitted (by sb) hu)
  refine ⟨?_, ?_⟩ <;> first | sb | ob))

theorem startPhase1_tb {T E : Int} {s s' : RState} {q i b : w32} {ps : List Proposal}
    {cs : List Cmd} {o : List Out} (hs : SB T E s) (hT : 0 ≤ T) (hE : 0 ≤ E)
    (h : startPhase1 s q i b ps cs = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  unfold startPhase1 at h; peel h
  all_goals (cases h; tb_fin)

theorem leaderCommit_tb {T E : Int} {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (hs : SB T E s) (hT : 0 ≤ T) (hE : 0 ≤ E) (hc : CB T E { c with status := St.COMMITTED, lb := some lb })
    (h : leaderCommit s q i c lb = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  have hb : TB T E c.base.t := hc.1
  unfold leaderCommit at h; peel h
  all_goals (cases h; tb_fin)

theorem handleExecuted_tb {T E : Int} {s s' : RState} {m : ExecutedM} {o : List Out}
    (hs : SB T E s) (hT : 0 ≤ T) (hE : 0 ≤ E)
    (h : handleExecuted s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  unfold handleExecuted at h; peel h
  all_goals (cases h; tb_fin)

macro "tb_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; tb_fin; done)
    | exact leaderCommit_tb (by sb) ‹_› ‹_› (by cb) $h:ident
    | exact startPhase1_tb (by sb) ‹_› ‹_› $h:ident
    | exact handleExecuted_tb (by sb) ‹_› ‹_› $h:ident)))

section
variable {T E : Int} {s s' : RState} {o : List Out} (hs : SB T E s) (hT : 0 ≤ T) (hE : 0 ≤ E)
include hs hT hE

theorem stepPreAccept_tb {m : PreAcceptM} (hm : MB T E (.preAccept m))
    (h : stepPreAccept s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  simp only [MB] at hm; unfold stepPreAccept at h; tb_close h

theorem stepPreAcceptReply_tb {m : PreAcceptReplyM} (hm : MB T E (.preAcceptReply m))
    (h : stepPreAcceptReply s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  simp only [MB] at hm; unfold stepPreAcceptReply at h; tb_close h

theorem stepPreAcceptOK_tb {m : PreAcceptOKM}
    (h : stepPreAcceptOK s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  unfold stepPreAcceptOK at h; tb_close h

theorem stepAccept_tb {m : EAcceptM} (hm : MB T E (.accept m))
    (h : stepAccept s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  simp only [MB] at hm; unfold stepAccept at h; tb_close h

theorem stepAcceptReply_tb {m : AcceptReplyM}
    (h : stepAcceptReply s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  unfold stepAcceptReply at h; tb_close h

theorem stepCommit_tb {m : ECommitM} (hm : MB T E (.commit m))
    (h : stepCommit s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  simp only [MB] at hm; unfold stepCommit at h; tb_close h

theorem stepPrepare_tb {m : PrepareM}
    (h : stepPrepare s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  unfold stepPrepare at h; tb_close h

theorem stepPrepareReply_tb {m : PrepareReplyM} (hm : MB T E (.prepareReply m))
    (h : stepPrepareReply s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  simp only [MB] at hm; unfold stepPrepareReply at h; tb_close h

theorem stepRecover_tb {q i : w32}
    (h : stepRecover s q i = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  unfold stepRecover at h; tb_close h

theorem stepRead1_tb {m : Read1ProxiedM} (hm : MB T E (.read1 m))
    (h : stepRead1 s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  simp only [MB] at hm; obtain ⟨hm1, hm2⟩ := hm; unfold stepRead1 at h; tb_close h

theorem stepRead2_tb {m : Read2ProxiedM} (hm : MB T E (.read2 m))
    (h : stepRead2 s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  simp only [MB] at hm; unfold stepRead2 at h; tb_close h

theorem stepWrite2_tb {m : Write2ProxiedM} (hm : MB T E (.write2 m))
    (h : stepWrite2 s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  simp only [MB] at hm; have hsb := SB.overwrite hs hm (v := m.vt.v)
  unfold stepWrite2 at h; tb_close h

theorem stepExecuteOverwrite_tb {m : ExecuteOverwriteM} (hm : MB T E (.executeOverwrite m))
    (h : stepExecuteOverwrite s m = .ok (s', o)) : SB T E s' ∧ OB T E o := by
  simp only [MB] at hm; unfold stepExecuteOverwrite at h; tb_close h

end

end Perennial.gryff.pure.La

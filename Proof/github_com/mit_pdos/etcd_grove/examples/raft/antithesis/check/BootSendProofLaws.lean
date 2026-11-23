/-
Lean-first (no Rocq counterpart). #33 S3b W5 (2026-11-23): laws for the proofs of `Boot` and `Send`
(`State__Boot.lean`, `State__Send.lean`): `Boot`'s tail (after the restore) as a function of the
state it starts from, the restored log within budget, and a log field read from an owned successor.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.BootSendLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

set_option linter.unusedSimpArgs false

/-- `Boot`'s tail (B 182-194, after the restore), from the state `ns` the restore left. -/
def bootSendP_bootTail (s ns : State) (n : Nat) (ev : Event) : EvalM (Option State) := do
  let mut ns := ns
  let a ← if ev.applied.isSome then need ev.applied else pure 0
  let logn := ns.log[n]!
  if !(← orM (pure (a == 0))
        (andM (pure (decide (a ≤ logn.length) && decide (a ≤ s.chain.length)))
          (do entriesEqual (← subSeq s.chain 1 a) (← subSeq logn 1 a)))) then
    return none
  ns := { ns with lastApplied := s.lastApplied.set n a }
  let c ← confOf logn a s.initConf
  ns := { ns with config := s.config.set n c }
  ns := { ns with confAt := s.confAt.set n (← lastConf logn a) }
  if !(← sameConf ev c) then return none
  return some ns

/-- `Boot`'s tail after the applied index `a`. -/
def bootSendP_bootRest (s ns : State) (n : Nat) (ev : Event) (a : Int) : EvalM (Option State) := do
  let mut ns := ns
  let logn := ns.log[n]!
  if !(← orM (pure (a == 0))
        (andM (pure (decide (a ≤ logn.length) && decide (a ≤ s.chain.length)))
          (do entriesEqual (← subSeq s.chain 1 a) (← subSeq logn 1 a)))) then
    return none
  ns := { ns with lastApplied := s.lastApplied.set n a }
  let c ← confOf logn a s.initConf
  ns := { ns with config := s.config.set n c }
  ns := { ns with confAt := s.confAt.set n (← lastConf logn a) }
  if !(← sameConf ev c) then return none
  return some ns

/-- `Boot`'s tail: the applied index, then the rest. -/
theorem bootSendP_bootTail_ok {s ns : State} {n : Nat} {ev : Event} {o : Option State}
    (h : bootSendP_bootTail s ns n ev = .ok o) :
    ∃ a, (if ev.applied.isSome then need ev.applied else pure 0 : EvalM Int) = .ok a ∧
      bootSendP_bootRest s ns n ev a = .ok o := by
  unfold bootSendP_bootTail at h
  by_cases hap : ev.applied.isSome = true
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hap)] at h ⊢
    obtain ⟨a, ha, h⟩ := bind_ok h
    exact ⟨a, ha, h⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hap)] at h ⊢
    obtain ⟨a, ha, h⟩ := bind_ok h
    exact ⟨a, ha, h⟩

theorem bootSendP_w64_eq_zero {u : w64} : u = W64 0 ↔ sint.Z u = 0 := by
  constructor
  · intro h; subst h; rfl
  · intro h; word

/-- `ConfOf(l, a, s.InitConf())`'s premise, for a log within budget. -/
theorem bootSendP_confOf_bounded {s : State} {l : List Entry} {b E w : Nat} (hl : logWithin b E l)
    (hE : ((s.cfg.initVoters.length + (b + w + 1) * E : Nat) : Int) < 2 ^ 61) :
    ConfOf.Bounded l s.initConf := by
  unfold ConfOf.Bounded State.initConf Config.initConf
  have h := logWithin_chgSum hl
  have : b * E ≤ (b + w + 1) * E := Nat.mul_le_mul_right _ (by omega)
  simp only [List.length_nil, Nat.add_zero]
  omega

/-- The restored log `SubSeq(s.Log[n], 1, u.Keep) ++ u.Suffix` within budget. -/
theorem bootSendP_restored_log {s : State} {b E n : Nat} {u : Pre} {pre : List Entry}
    (hW : s.Within b E) (hu : s.undo[n]! = some u) (hpre : subSeq (s.log[n]!) 1 u.keep = .ok pre) :
    logWithin b E (pre ++ u.suffix) := by
  have hlog0 : logWithin b E (s.log[n]!) :=
    getElem!_mem' (α := List Entry) (P := fun l => logWithin b E l) hW.log ⟨Nat.zero_le _, fun x hx => by cases hx⟩
  have huw : u.Within b E := hW.undo _ (getElem!_some_mem hu) u rfl
  obtain ⟨-, -, -, -, -, -, -, hu8, hu9, -⟩ := huw
  have hpl := bootSend_subSeq_one_length hpre
  refine ⟨?_, fun e he => ?_⟩
  · simp only [List.length_append]
    have := hu8.1
    omega
  · rcases List.mem_append.1 he with he | he
    · exact hlog0.2 e (bootSend_subSeq_mem hpre he)
    · exact hu8.2 e he

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- An owned successor's struct opened to read its `Log` field. -/
theorem bootSendP_stateOwn_log (q : Loc) (s : State) :
    stateOwn (GF := GF) q s ⊢ ∃ g : G.State, q ↦ g ∗ logsRO g.Log' s.log ∗ ⌜s.Wf⌝ ∗ (q ↦ g -∗ stateOwn q s) := by
  iintro Hq
  iunfold stateOwn at Hq
  iNamed Hq
  icases Hf with #Hf
  ihave #Hf2 := Hf
  iNamed Hf2
  iexists g
  iframe Hp HLog
  isplitr
  · ipureintro; exact HWf
  iintro Hp
  iunfold stateOwn
  iexists g
  iframe Hp Hf

end iris

end AntCheck
end EtcdGrove
end Perennial

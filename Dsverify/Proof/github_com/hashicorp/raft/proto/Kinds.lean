/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/Kinds.lean (241f27e).
-/
/-
`proto` — the kinds of entries (for raft's `prepareLog`, whose default case panics): every entry
of every leader log is a command, a no-op or a configuration (`IKinds`). By log matching
(`LMok`) the same holds for every log the protocol knows of (`log_kinds`, `C_kinds`).

`IKinds` is kept beside `PInv` (the ghost layer carries `PInv σ ∧ IKinds σ`); the steps that
change a leader log preserve it (`becomeLeader_kinds`, `leaderAppend_kinds`), the others leave
the leader logs unchanged.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.Laws

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

/-- A command, a no-op, a barrier (stage 2) or a configuration. -/
def kindOk (e : Entry) : Prop :=
  e.kind = kCommand ∨ e.kind = kNoop ∨ e.kind = kBarrier ∨ e.kind = kConfig

/-- Every entry of every leader log has a known kind. -/
def IKinds (σ : PState) : Prop := ∀ T k e, ent (σ.llog T) k = some e → kindOk e

/-- Log matching locates an entry in its term's leader log. -/
theorem LMok_ent {σ : PState} {L : RLog} {k : Nat} {e : Entry} (hL : LMok σ L)
    (he : ent L k = some e) : ent (σ.llog e.term) k = some e := by
  have hl := ent_le_length he
  have a := hL k hl.1 hl.2
  rw [termAt_of_ent he] at a
  rw [← agree_ent a (Nat.le_refl _)]
  exact he

theorem init_kinds (srvs : List SID) (g : Entry) (cv : List w8 → List SID) (hgk : g.kind = kConfig) :
    IKinds (init srvs g cv) := by
  intro T k e he
  show kindOk e
  have he' : ent (if T = 1 then [g] else []) k = some e := he
  split at he'
  · have hk := ent_le_length he'
    have : k = 1 := by simp at hk; omega
    subst this
    simp [ent] at he'; subst he'
    right; right; right; exact hgk
  · have hk := ent_le_length he'; simp at hk; omega

theorem becomeLeader_kinds (σ : PState) (c : SID) (h : PInv σ) (hp : becomeLeaderPre σ c)
    (hK : IKinds σ) : IKinds (becomeLeader σ c) := by
  intro T k e he
  simp only [becomeLeader] at he
  split at he
  · simp only [updT] at he
    split at he
    · exact hK _ _ _ (LMok_ent (h.2.2.1.1 c hp.1).1 he)
    · exact hK _ _ _ he
  · exact hK _ _ _ he
  /- stage-3 proof:
  := by
  intro T k e he
  simp only [becomeLeader] at he
  split at he
  · simp only [updT] at he
    split at he
    · exact hK _ _ _ (LMok_ent (h.2.2.1.1 c hp.1).1 he)
    · exact hK _ _ _ he
  · exact hK _ _ _ he
  -/

theorem leaderAppend_kinds (σ : PState) (i : SID) (es : RLog) (h : PInv σ)
    (hp : leaderAppendPre σ i es) (hK : IKinds σ) : IKinds (leaderAppend σ i es) := by
  intro T k e he
  rw [la_llog h hp] at he
  split at he
  · by_cases hk : k ≤ (σ.llog T).length
    · rw [ent_append_left _ _ _ hk] at he; exact hK _ _ _ he
    · rcases (hp.2.2 e (ent_append_mem he (by omega))).2 with h1 | h1 | h1
      · left; exact h1
      · right; left; exact h1
      · right; right; left; exact h1
  · exact hK _ _ _ he

/-- (stage 4) A configuration entry keeps the kinds known. -/
theorem leaderAppendCfg_kinds (σ : PState) (i : SID) (e : Entry) (h : PInv σ)
    (hp : leaderAppendCfgPre σ i e) (hK : IKinds σ) : IKinds (leaderAppendCfg σ i e) := by
  obtain ⟨hi, hld, het, hek, _⟩ := hp
  have hb : laBase σ i [e] := ⟨hi, hld, fun e' he' => by simp at he'; subst he'; exact het⟩
  intro T k e' he
  unfold leaderAppendCfg at he
  rw [lab_llog h hb] at he
  split at he
  · by_cases hk : k ≤ (σ.llog T).length
    · rw [ent_append_left _ _ _ hk] at he; exact hK _ _ _ he
    · have := ent_append_mem he (by omega)
      simp at this; subst this
      right; right; right; exact hek
  · exact hK _ _ _ he

/-- (stage 4) Installing a configuration in the commitment keeps the kinds (no log changes). -/
theorem installCfg_kinds (σ : PState) (T : Nat) (hK : IKinds σ) : IKinds (installCfg σ T) := by
  intro T' k e he
  exact hK T' k e he

/-- Every entry of a server's log has a known kind. -/
theorem log_kinds (σ : PState) (i : SID) (k : Nat) (e : Entry) :
    PInv σ → IKinds σ → i ∈ σ.srvs → ent (σ.log i) k = some e →
      e.kind = kCommand ∨ e.kind = kNoop ∨ e.kind = kBarrier ∨ e.kind = kConfig := by
  intro h hK hi he
  exact hK _ _ _ (LMok_ent (h.2.2.1.1 i hi).1 he)

/-- Every entry of the committed log has a known kind. -/
theorem C_kinds (σ : PState) (k : Nat) (e : Entry) :
    PInv σ → IKinds σ → ent σ.C k = some e →
      e.kind = kCommand ∨ e.kind = kNoop ∨ e.kind = kBarrier ∨ e.kind = kConfig := by
  intro h hK he
  exact hK _ _ _ (C_llog σ k e h he)

end proto
end github_com.hashicorp.raft
end Perennial

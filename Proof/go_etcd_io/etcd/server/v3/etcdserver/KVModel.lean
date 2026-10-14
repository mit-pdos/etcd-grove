/-
**The KV model of the committed raft log: where the apply relation meets it** (unit T1,
2026-10-14; the definitions: `KVModelDefs.lean`). Pure. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.etcd.server.v3.etcdserver

/-! ## Where the apply relation departs from the function -/

/-- **The backend's relation on a plain request is the function.** -/
theorem backendStep_plain (rq : apply.IRRModel) (log : mvcc.Log) (o : apply.Outcome)
    (hp : plainReq rq) (h : apply.backendStep rq log o) :
    o.logAfter log = backendLog rq log := by
  unfold plainReq at hp
  unfold apply.backendStep at h
  unfold backendLog
  cases hk : apply.dispatchKind rq <;> simp only [hk] at hp h ⊢
  case put =>
    obtain ⟨op, hop, h⟩ := h
    obtain ⟨-, -, hp⟩ := hp
    obtain ⟨hl, hn⟩ := hp op hop
    simp only [hop]
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ | h
    · exact absurd hl h
    · rw [hn] at h; cases h
    · rw [h]; rfl
  case deleteRange =>
    obtain ⟨op, hop, h⟩ := h
    obtain ⟨-, -, hp⟩ := hp
    simp only [hop]
    rcases h with h | ⟨h, -⟩
    · rw [h]; rfl
    · rw [hp op hop] at h; cases h
  case range => rw [h]; rfl
  all_goals (rcases h with h | h <;> (rw [h]; rfl))

/-- **The chain's relation on a plain request is the function, or an auth rejection by an
enabled auth layer.** -/
theorem chainStep_plain : ∀ (c : apply.Chain) (rq : apply.IRRModel) (log : mvcc.Log)
    (o : apply.Outcome), plainReq rq → apply.chainStep apply.backendStep c rq log o →
      o.logAfter log = chainLog c rq log ∨ (o = .rejected .auth ∧ c.authOn = true)
  | .backend, rq, log, o, hp, h => Or.inl (backendStep_plain rq log o hp h)
  | .corrupt c, rq, log, o, hp, h => by
    simp only [apply.chainStep] at h
    simp only [chainLog, apply.Chain.authOn]
    split at h
    · rename_i hk; rw [if_pos hk, h]; left; rfl
    · rename_i hk; rw [if_neg hk]; exact chainStep_plain c rq log o hp h
  | .capped c, rq, log, o, hp, h => by
    simp only [apply.chainStep] at h
    simp only [chainLog, apply.Chain.authOn]
    split at h
    · rename_i hk; rw [if_pos hk, h]; left; rfl
    · rename_i hk
      rw [if_neg hk]
      split at h
      · rename_i ht
        unfold plainReq at hp; rw [ht] at hp; exact hp.elim
      · exact chainStep_plain c rq log o hp h
  | .auth on c, rq, log, o, hp, h => by
    simp only [apply.chainStep] at h
    simp only [chainLog, apply.Chain.authOn]
    split at h
    · rcases h with ⟨hm, h⟩ | h
      · cases hon : on
        · -- auth disabled: the rejection is of a request whose log does not change
          rw [hon] at hm
          have hk : apply.dispatchKind rq ≠ .put ∧ apply.dispatchKind rq ≠ .deleteRange := by
            unfold plainReq at hp
            rcases hm with hm | hm | hm
            · cases hm
            · constructor
              · intro hk; rw [hk] at hp; rw [hp.2.1] at hm; cases hm
              · intro hk; rw [hk] at hp; rw [hp.2.1] at hm; cases hm
            · exact ⟨hm.1, hm.2.2⟩
          left; rw [h, chainLog_nonwrite rq log hk c]; rfl
        · right; exact ⟨h, rfl⟩
      · rcases chainStep_plain c rq log o hp h with h | ⟨h1, h2⟩
        · left; exact h
        · right; exact ⟨h1, by simp [h2]⟩
    · rcases chainStep_plain c rq log o hp h with h | ⟨h1, h2⟩
      · left; exact h
      · right; exact ⟨h1, by simp [h2]⟩
  | .quota c, rq, log, o, hp, h => by
    simp only [apply.chainStep] at h
    simp only [chainLog, apply.Chain.authOn]
    exact chainStep_plain c rq log o hp h

/-- **`dispatch`'s relation on a plain request is the function, or an enabled auth layer's
rejection.** -/
theorem dispatchStep_plain (c : apply.Chain) (rq : apply.IRRModel) (v3 : Bool) (log : mvcc.Log)
    (o : apply.Outcome) (hp : plainReq rq) (h : apply.dispatchStep c rq v3 log o) :
    o.logAfter log = dispatchLog c rq v3 log ∨ (o = .rejected .auth ∧ c.authOn = true) := by
  unfold apply.dispatchStep at h
  unfold dispatchLog
  split at h
  · rename_i hc; rw [if_pos hc, h]; left; rfl
  · rename_i hc
    rw [if_neg hc]
    split at h
    · rename_i hs; rw [if_pos hs]; exact chainStep_plain c rq log o hp h
    · rename_i hs; rw [if_neg hs]; left; exact h

/-- A plain request is not an alarm request. -/
theorem plainReq_not_alarm (rq : apply.IRRModel) (hp : plainReq rq) :
    apply.dispatchKind rq ≠ .alarm := by
  intro hk; unfold plainReq at hp; rw [hk] at hp; exact hp

/-- **`apply.Apply`'s relation on a plain request**: the chain unchanged, and the log as
`dispatchLog` says, unless the chain's auth layer is enabled and rejected it (the log unchanged).
A skipped or admin-rejected request changes nothing, and `dispatchLog` agrees: a plain request
that `Apply` may skip or reject is no put and no delete. -/
theorem applyStep_plain (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (hp : plainReq rq) (h : apply.applyStep rq v3 x x' out) :
    x'.chain = x.chain ∧
      (x'.log = dispatchLog x.chain rq v3 x.log ∨ (x.chain.authOn = true ∧ x'.log = x.log)) := by
  have hnochg : (apply.noSideEffect rq = true ∨ apply.needAdminPermission rq = true) →
      dispatchLog x.chain rq v3 x.log = x.log := by
    intro hn
    unfold dispatchLog
    split
    · rfl
    · split
      · have hk : apply.dispatchKind rq ≠ .put ∧ apply.dispatchKind rq ≠ .deleteRange := by
          unfold plainReq at hp
          constructor
          · intro hk; rw [hk] at hp; rcases hn with hn | hn
            · rw [hp.1] at hn; cases hn
            · rw [hp.2.1] at hn; cases hn
          · intro hk; rw [hk] at hp; rcases hn with hn | hn
            · rw [hp.1] at hn; cases hn
            · rw [hp.2.1] at hn; cases hn
        exact chainLog_nonwrite rq x.log hk _
      · rfl
  cases out with
  | skipped =>
    obtain ⟨hn, rfl⟩ := h
    exact ⟨rfl, Or.inl (hnochg (Or.inl hn)).symm⟩
  | rejected =>
    obtain ⟨hn, rfl⟩ := h
    exact ⟨rfl, Or.inl (hnochg (Or.inr hn)).symm⟩
  | dispatched o skip =>
    obtain ⟨-, hd, hl, hc⟩ := h
    have hchain : x'.chain = x.chain := by
      rcases hc with hc | ⟨-, hk, -⟩
      · exact hc
      · exact absurd hk (plainReq_not_alarm rq hp)
    refine ⟨hchain, ?_⟩
    rcases dispatchStep_plain x.chain rq v3 x.log o hp hd with h' | ⟨h', hon⟩
    · left; rw [hl, h']
    · right; refine ⟨hon, ?_⟩; rw [hl, h']; rfl

/-- **A raft entry's step on a plain entry, auth disabled**: the chain unchanged, and the log as
`kvEntry` says. -/
theorem batchStep_plain (c₀ : w64) (m : EntryModel) (x x' : apply.ApplyKV)
    (hp : plainEntry m) (hoff : x.chain.authOn = false) (h : batchStep c₀ m x x') :
    x'.chain = x.chain ∧ x'.log = kvEntry c₀ x.chain x.log m := by
  unfold batchStep at h
  unfold kvEntry
  split at h
  · rename_i ht
    rw [if_pos ht]
    obtain ⟨out, h⟩ := h
    unfold entryStep at h
    split at h
    · rename_i hd
      obtain ⟨rfl, -⟩ := h
      rw [if_pos hd]
      exact ⟨rfl, rfl⟩
    · rename_i hd
      rw [if_neg hd]
      obtain ⟨rq, id, hdec, -, h⟩ := h
      rw [hdec]
      obtain ⟨hc, h⟩ := applyStep_plain rq _ x x' out (hp ht hd rq hdec) h
      refine ⟨hc, ?_⟩
      rcases h with h | ⟨hon, -⟩
      · exact h
      · rw [hoff] at hon; cases hon
  · rename_i ht
    rw [if_neg ht]
    subst h
    exact ⟨rfl, rfl⟩

/-- **The apply relation on a plain log, auth disabled, is the model**: the chain unchanged and
the log `kvRaftOf` of the entries. -/
theorem entriesStep_plain (c₀ : w64) (A : List EntryModel) :
    ∀ (x x' : apply.ApplyKV), plainLog A → x.chain.authOn = false → entriesStep c₀ A x x' →
      x'.chain = x.chain ∧ x'.log = kvRaftOf c₀ x.chain x.log A := by
  induction A with
  | nil => intro x x' _ _ h; simp only [entriesStep] at h; subst h; exact ⟨rfl, rfl⟩
  | cons m A ih =>
    intro x x' hp hoff h
    obtain ⟨x1, h1, h2⟩ := h
    have hp' : plainLog A := fun m' hm' => hp m' (List.mem_cons_of_mem _ hm')
    obtain ⟨hc1, hl1⟩ := batchStep_plain c₀ m x x1 (hp m (List.mem_cons_self ..)) hoff h1
    obtain ⟨hc2, hl2⟩ := ih x1 x' hp' (by rw [hc1]; exact hoff) h2
    refine ⟨hc2.trans hc1, ?_⟩
    rw [hl2, hc1, hl1]
    rfl

end EtcdGrove
end Perennial

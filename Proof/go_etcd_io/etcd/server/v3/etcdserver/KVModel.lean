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

/-- A chain without a capped layer (2026-10-15, unit T2: the capped layer may reject a
transaction or not, its cost being opaque). -/
def apply.Chain.capFree : apply.Chain → Bool
  | .backend => true
  | .auth _ c => c.capFree
  | .quota c => c.capFree
  | .capped _ => false
  | .corrupt c => c.capFree

/-- **A chain on which the apply relation is the KV model** (2026-10-15, unit T2): auth disabled
(`authOn`) and no capped layer (`capFree`); the start's chain, `alarmChain false false false`. -/
def apply.Chain.kvExact (c : apply.Chain) : Bool := !c.authOn && c.capFree

@[simp] theorem alarmChain_kvExact : (apply.alarmChain false false false).kvExact = true := rfl

/-- **The backend's relation on a plain request is the function.** -/
theorem backendStep_plain (rq : apply.IRRModel) (log : mvcc.Log) (o : apply.Outcome)
    (hp : plainCover rq) (h : apply.backendStep rq log o) :
    o.logAfter log = backendLog rq log := by
  unfold plainCover at hp
  unfold apply.backendStep at h
  unfold backendLog
  cases hk : apply.dispatchKind rq <;> simp only [hk] at hp h ⊢
  case put =>
    obtain ⟨op, hop, h⟩ := h
    obtain ⟨-, -, hp⟩ := hp
    have hl := hp op hop
    simp only [hop]
    rcases h with ⟨h, -⟩ | ⟨hn, hf, rfl⟩ | ⟨hs, rfl⟩
    · exact absurd hl h
    · rw [hn, hf]; rfl
    · have : (txn.needsPrev op && (mvcc.findKey op.key (mvcc.stateAfter log)).isNone) = false := by
        cases hn : txn.needsPrev op
        · rfl
        · have := hs hn
          cases hf : mvcc.findKey op.key (mvcc.stateAfter log)
          · rw [hf] at this; cases this
          · rfl
      rw [this]; rfl
  case deleteRange =>
    obtain ⟨op, hop, rfl⟩ := h
    simp only [hop]
    rfl
  case txn =>
    obtain ⟨t, hop, h⟩ := h
    obtain ⟨-, -, hp⟩ := hp
    simp only [hop]
    rcases h with ⟨rfl, hn⟩ | ⟨rfl, -, hig⟩
    · rw [if_neg (hn (hp t hop))]; rfl
    · rw [if_pos hig]; rfl
  all_goals (rcases h with h | h <;> (rw [h]; rfl))

/-- **The chain's relation on a plain request is the function**, unless the chain is not
`kvExact` and the request was rejected (the log unchanged): an enabled auth layer's rejection, or
a capped layer's. -/
theorem chainStep_plain : ∀ (c : apply.Chain) (rq : apply.IRRModel) (log : mvcc.Log)
    (o : apply.Outcome), plainCover rq → apply.chainStep apply.backendStep c rq log o →
      o.logAfter log = chainLog c rq log ∨ (o.logAfter log = log ∧ c.kvExact = false)
  | .backend, rq, log, o, hp, h => Or.inl (backendStep_plain rq log o hp h)
  | .corrupt c, rq, log, o, hp, h => by
    simp only [apply.chainStep] at h
    simp only [chainLog, apply.Chain.kvExact, apply.Chain.authOn, apply.Chain.capFree]
    split at h
    · rename_i hk; rw [if_pos hk, h]; left; rfl
    · rename_i hk; rw [if_neg hk]; exact chainStep_plain c rq log o hp h
  | .capped c, rq, log, o, hp, h => by
    simp only [apply.chainStep] at h
    simp only [chainLog, apply.Chain.kvExact, apply.Chain.authOn, apply.Chain.capFree]
    split at h
    · rename_i hk; rw [if_pos hk, h]; left; rfl
    · rename_i hk
      rw [if_neg hk]
      split at h
      · rcases h with h | h
        · right; rw [h]; exact ⟨rfl, by simp⟩
        · rcases chainStep_plain c rq log o hp h with h | ⟨h, -⟩
          · left; exact h
          · right; exact ⟨h, by simp⟩
      · rcases chainStep_plain c rq log o hp h with h | ⟨h, -⟩
        · left; exact h
        · right; exact ⟨h, by simp⟩
  | .auth on c, rq, log, o, hp, h => by
    simp only [apply.chainStep] at h
    simp only [chainLog]
    have hlift : c.kvExact = false → (apply.Chain.auth on c).kvExact = false := by
      simp only [apply.Chain.kvExact, apply.Chain.authOn, apply.Chain.capFree]
      intro h; cases ho : on <;> cases ha : c.authOn <;> simp_all
    split at h
    · rcases h with ⟨hm, h⟩ | h
      · cases hon : on
        · -- auth disabled: the rejection is of a request whose log does not change
          rw [hon] at hm
          have hk : ¬ writeKind (apply.dispatchKind rq) := by
            unfold plainCover at hp
            unfold writeKind
            rcases hm with hm | hm | hm
            · cases hm
            · rintro (hk | hk | hk) <;> rw [hk] at hp <;>
                first | (rw [hp.2.1] at hm; cases hm) | (rw [hp.2] at hm; cases hm)
            · rintro (hk | hk | hk)
              · exact hm.1 hk
              · exact hm.2.2.1 hk
              · exact hm.2.2.2 hk
          left; rw [h, chainLog_nonwrite rq log hk c]; rfl
        · right; rw [h]
          exact ⟨rfl, by simp [apply.Chain.kvExact, apply.Chain.authOn]⟩
      · rcases chainStep_plain c rq log o hp h with h | ⟨h1, h2⟩
        · left; exact h
        · right; exact ⟨h1, hlift h2⟩
    · rcases chainStep_plain c rq log o hp h with h | ⟨h1, h2⟩
      · left; exact h
      · right; exact ⟨h1, hlift h2⟩
  | .quota c, rq, log, o, hp, h => by
    simp only [apply.chainStep] at h
    simp only [chainLog, apply.Chain.kvExact, apply.Chain.authOn, apply.Chain.capFree]
    exact chainStep_plain c rq log o hp h

/-- **`dispatch`'s relation on a plain request is the function**, unless the chain is not
`kvExact` and the log is unchanged. -/
theorem dispatchStep_plain (c : apply.Chain) (rq : apply.IRRModel) (v3 : Bool) (log : mvcc.Log)
    (o : apply.Outcome) (hp : plainCover rq) (h : apply.dispatchStep c rq v3 log o) :
    o.logAfter log = dispatchLog c rq v3 log ∨ (o.logAfter log = log ∧ c.kvExact = false) := by
  unfold apply.dispatchStep at h
  unfold dispatchLog
  split at h
  · rename_i hc; rw [if_pos hc, h]; left; rfl
  · rename_i hc
    rw [if_neg hc]
    split at h
    · rename_i hs; rw [if_pos hs]; exact chainStep_plain c rq log o hp h
    · rename_i hs; rw [if_neg hs]; left; exact h

/-- A covered request is not an alarm request. -/
theorem plainReq_not_alarm (rq : apply.IRRModel) (hp : plainCover rq) :
    apply.dispatchKind rq ≠ .alarm := by
  intro hk; unfold plainCover at hp; rw [hk] at hp; exact hp

/-- **`apply.Apply`'s relation on a plain request**: the chain unchanged, and the log as
`dispatchLog` says, unless the chain is not `kvExact` (the log unchanged). A skipped or
admin-rejected request changes nothing, and `dispatchLog` agrees: a plain request that `Apply`
may skip or reject is no put, no delete and no transaction. -/
theorem applyStep_plain (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (hp : plainCover rq) (h : apply.applyStep rq v3 x x' out) :
    x'.chain = x.chain ∧
      (x'.log = dispatchLog x.chain rq v3 x.log ∨ (x.chain.kvExact = false ∧ x'.log = x.log)) := by
  have hnochg : (apply.noSideEffect rq = true ∨ apply.needAdminPermission rq = true) →
      dispatchLog x.chain rq v3 x.log = x.log := by
    intro hn
    unfold dispatchLog
    split
    · rfl
    · split
      · have hk : ¬ writeKind (apply.dispatchKind rq) := by
          unfold plainCover at hp
          unfold writeKind
          rintro (hk | hk | hk) <;> rw [hk] at hp <;> rcases hn with hn | hn
          all_goals first | (rw [hp.1] at hn; cases hn) | (rw [hp.2.1] at hn; cases hn) |
            (rw [hp.2] at hn; cases hn)
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
    · right; refine ⟨hon, ?_⟩; rw [hl, h']

/-- **A raft entry's step on a plain entry, at a `kvExact` chain**: the chain unchanged, and the
log as `kvEntry` says. -/
theorem batchStep_plain (c₀ : w64) (m : EntryModel) (x x' : apply.ApplyKV)
    (hp : plainEntry m) (hoff : x.chain.kvExact = true) (h : batchStep c₀ m x x') :
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
      obtain ⟨hc, h⟩ := applyStep_plain rq _ x x' out (hp ht hd rq hdec).1 h
      refine ⟨hc, ?_⟩
      rcases h with h | ⟨hon, -⟩
      · exact h
      · rw [hoff] at hon; cases hon
  · rename_i ht
    rw [if_neg ht]
    subst h
    exact ⟨rfl, rfl⟩

end EtcdGrove
end Perennial

/-
**The KV model of the committed raft log** (unit T1, 2026-10-14; `notes/decisions.md`, "Put and Get
as persistent atomic updates linearized by raft"). Pure. Lean-first (no Rocq counterpart).

A persistent atomic update fires at **commit**, before any member applies the entry, so the KV
state after a committed log must be a function of the log. The apply package's model
(`apply.applyStep`, `apply.chainStep`) is a relation. This file gives the function, `kvOf`, and
says exactly where the relation departs from it.

- **Plain requests** (`plainReq`): a put with lease `0` and no ignore flags, a range, a delete
  without `PrevKv`, or a request that does not touch the store. A put or delete must not also
  carry a field that makes `Apply` skip it (`noSideEffect`) or check admin permission
  (`needAdminPermission`). Excluded: txn, compaction, lease grant and revocation, alarm requests
  and `AuthEnable` (their outcomes, or the outcomes of later requests, depend on stores that the
  model treats as oracles).
- **The deterministic step** (`chainLog`, `dispatchLog`, `kvEntry`) and the fold `kvOf c₀ ch log₀
  A` over raft entries: an empty entry, a conf change and an entry at or below the consistent
  index `c₀` change nothing.
- **Where the relation departs from it** (`applyStep_plain`, `batchStep_plain`): for a plain
  request, every outcome the relation allows changes the log as `dispatchLog` does, leaves the
  chain alone, or is an **auth rejection** (`.rejected .auth`, the log unchanged). The model
  allows the auth layer to reject whatever the store's state. Excluding that needs the auth
  layer's mode in the model (`authOn`, the next step: `notes/decisions.md`).
- **Shape** (`kvEntry_grow`, `kvOf_prefix`) and the **intermediate value lemma** (`kvOf_ivt`): a log
  between `kvOf A₀` and `kvOf B` (prefix order) is `kvOf A` for some `A` between `A₀` and `B`,
  because each entry appends at most one revision.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.etcd.server.v3.etcdserver

/-! ## Plain requests and entries -/

/-- **A plain request**: one whose effect on the KV is a function of the log (see the file
header). -/
def plainReq (rq : apply.IRRModel) : Prop :=
  match apply.dispatchKind rq with
  | .put => apply.noSideEffect rq = false ∧ apply.needAdminPermission rq = false ∧
      ∀ op, rq.put = some op → op.leaseID = W64 0 ∧ txn.needsPrev op = false
  | .deleteRange => apply.noSideEffect rq = false ∧ apply.needAdminPermission rq = false ∧
      ∀ op, rq.deleteRange = some op → op.base.prevKV = false
  | .txn | .compaction | .leaseGrant | .leaseRevoke | .alarm | .authEnable | .none => False
  | _ => True

/-- **A plain entry**: a normal entry with data decodes to a plain request (an empty entry and a
conf change are plain). -/
def plainEntry (m : EntryModel) : Prop :=
  m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq → plainReq rq

/-- **A plain log**: every entry plain. -/
def plainLog (A : List EntryModel) : Prop := ∀ m ∈ A, plainEntry m

theorem plainLog_append (A B : List EntryModel) :
    plainLog (A ++ B) ↔ plainLog A ∧ plainLog B := by
  unfold plainLog
  simp only [List.mem_append]
  constructor
  · intro h; exact ⟨fun m hm => h m (Or.inl hm), fun m hm => h m (Or.inr hm)⟩
  · rintro ⟨h1, h2⟩ m (hm | hm)
    · exact h1 m hm
    · exact h2 m hm

/-! ## The deterministic step -/

/-- The backend's effect on the log, deterministically (`apply.backendStep`'s applied outcome for
a plain request). -/
def backendLog (rq : apply.IRRModel) (log : mvcc.Log) : mvcc.Log :=
  match apply.dispatchKind rq with
  | .put =>
      match rq.put with
      | some op => log ++ [[txn.putChangeOf op (mvcc.findKey op.key (mvcc.stateAfter log))]]
      | none => log
  | .deleteRange =>
      match rq.deleteRange with
      | some op => mvcc.commitLog log (txn.delChanges (mvcc.stateAfter log) op)
      | none => log
  | _ => log

/-- **The chain's effect on the log**, deterministically: the corrupt and capped layers reject
what they always reject; the auth layer lets everything through (auth disabled); the quota layer
changes no log. -/
def chainLog : apply.Chain → apply.IRRModel → mvcc.Log → mvcc.Log
  | .backend, rq, log => backendLog rq log
  | .corrupt c, rq, log =>
      if apply.corruptRejects (apply.dispatchKind rq) then log else chainLog c rq log
  | .capped c, rq, log =>
      if apply.cappedRejects (apply.dispatchKind rq) then log else chainLog c rq log
  | .auth c, rq, log => chainLog c rq log
  | .quota c, rq, log => chainLog c rq log

/-- **`dispatch(rq, v3)`'s effect on the log**, deterministically (`apply.dispatchStep`). -/
def dispatchLog (c : apply.Chain) (rq : apply.IRRModel) (v3 : Bool) (log : mvcc.Log) :
    mvcc.Log :=
  if apply.preV3Kind (apply.dispatchKind rq) = true ∨ v3 = false then log
  else if apply.storeKind (apply.dispatchKind rq) = true then chainLog c rq log
  else log

/-- **An entry's effect on the log**, from the consistent index `c₀` with the chain `ch`: a normal
entry with data that decodes is dispatched (`v3` iff above `c₀`); nothing else changes the log. -/
def kvEntry (c₀ : w64) (ch : apply.Chain) (log : mvcc.Log) (m : EntryModel) : mvcc.Log :=
  if m.typ = W32 0 then
    if m.data = [] then log
    else match apply.irrDecode m.data with
      | some rq => dispatchLog ch rq (decide (uint.Z c₀ < uint.Z m.index)) log
      | none => log
  else log

/-- **The KV model of a raft log** `A` (the entries after the start index), from the log `log₀`
at the start (the snapshot's), the consistent index `c₀` and the chain `ch`. -/
def kvOf (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) (A : List EntryModel) : mvcc.Log :=
  A.foldl (kvEntry c₀ ch) log₀

/-- **The value of `k`** in the state after `log`. -/
def kvVal (log : mvcc.Log) (k : GoString) : Option GoString :=
  (mvcc.findKey k (mvcc.stateAfter log)).map EtcdKv.value

theorem kvOf_nil (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) : kvOf c₀ ch log₀ [] = log₀ := rfl

theorem kvOf_append (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) (A B : List EntryModel) :
    kvOf c₀ ch log₀ (A ++ B) = kvOf c₀ ch (kvOf c₀ ch log₀ A) B := by
  unfold kvOf; exact List.foldl_append

theorem kvOf_snoc (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) (A : List EntryModel)
    (m : EntryModel) : kvOf c₀ ch log₀ (A ++ [m]) = kvEntry c₀ ch (kvOf c₀ ch log₀ A) m := by
  rw [kvOf_append]; rfl

/-! ## Shape: at most one revision per entry -/

theorem commitLog_grow' (log : mvcc.Log) (pend : List mvcc.Change) :
    mvcc.commitLog log pend = log ∨ ∃ cs, mvcc.commitLog log pend = log ++ [cs] := by
  unfold mvcc.commitLog
  split
  · left; rfl
  · right; exact ⟨_, rfl⟩

theorem backendLog_grow (rq : apply.IRRModel) (log : mvcc.Log) :
    backendLog rq log = log ∨ ∃ cs, backendLog rq log = log ++ [cs] := by
  unfold backendLog
  split
  · split
    · right; exact ⟨_, rfl⟩
    · left; rfl
  · split
    · exact commitLog_grow' _ _
    · left; rfl
  · left; rfl

theorem chainLog_grow : ∀ (c : apply.Chain) (rq : apply.IRRModel) (log : mvcc.Log),
    chainLog c rq log = log ∨ ∃ cs, chainLog c rq log = log ++ [cs]
  | .backend, rq, log => backendLog_grow rq log
  | .corrupt c, rq, log => by
    simp only [chainLog]; split
    · left; rfl
    · exact chainLog_grow c rq log
  | .capped c, rq, log => by
    simp only [chainLog]; split
    · left; rfl
    · exact chainLog_grow c rq log
  | .auth c, rq, log => by simp only [chainLog]; exact chainLog_grow c rq log
  | .quota c, rq, log => by simp only [chainLog]; exact chainLog_grow c rq log

theorem dispatchLog_grow (c : apply.Chain) (rq : apply.IRRModel) (v3 : Bool) (log : mvcc.Log) :
    dispatchLog c rq v3 log = log ∨ ∃ cs, dispatchLog c rq v3 log = log ++ [cs] := by
  unfold dispatchLog
  split
  · left; rfl
  · split
    · exact chainLog_grow c rq log
    · left; rfl

/-- **An entry appends at most one revision.** -/
theorem kvEntry_grow (c₀ : w64) (ch : apply.Chain) (log : mvcc.Log) (m : EntryModel) :
    kvEntry c₀ ch log m = log ∨ ∃ cs, kvEntry c₀ ch log m = log ++ [cs] := by
  unfold kvEntry
  split
  · split
    · left; rfl
    · split
      · exact dispatchLog_grow _ _ _ _
      · left; rfl
  · left; rfl

theorem kvEntry_prefix (c₀ : w64) (ch : apply.Chain) (log : mvcc.Log) (m : EntryModel) :
    log <+: kvEntry c₀ ch log m := by
  rcases kvEntry_grow c₀ ch log m with h | ⟨cs, h⟩
  · rw [h]; exact List.prefix_refl _
  · rw [h]; exact List.prefix_append _ _

theorem kvOf_extends (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) (A : List EntryModel) :
    log₀ <+: kvOf c₀ ch log₀ A := by
  induction A generalizing log₀ with
  | nil => exact List.prefix_refl _
  | cons m A ih =>
    show log₀ <+: kvOf c₀ ch (kvEntry c₀ ch log₀ m) A
    exact (kvEntry_prefix c₀ ch log₀ m).trans (ih _)

/-- **The model grows with the raft log.** -/
theorem kvOf_prefix (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) (A B : List EntryModel)
    (h : A <+: B) : kvOf c₀ ch log₀ A <+: kvOf c₀ ch log₀ B := by
  obtain ⟨D, rfl⟩ := h
  rw [kvOf_append]
  exact kvOf_extends _ _ _ _

/-- The intermediate value lemma, from a log: a log between `log` and the fold of `D` from it is
the fold of a prefix of `D`. -/
theorem kvOf_ivt_aux (c₀ : w64) (ch : apply.Chain) (l : mvcc.Log) :
    ∀ (D : List EntryModel) (log : mvcc.Log), log <+: l → l <+: kvOf c₀ ch log D →
      ∃ D', D' <+: D ∧ kvOf c₀ ch log D' = l
  | [], log, h1, h2 => ⟨[], List.prefix_refl _, h1.eq_of_length (Nat.le_antisymm h1.length_le h2.length_le)⟩
  | m :: D, log, h1, h2 => by
    by_cases he : log = l
    · exact ⟨[], List.nil_prefix, he⟩
    · have h2' : l <+: kvOf c₀ ch (kvEntry c₀ ch log m) D := h2
      have hstep : kvEntry c₀ ch log m <+: l := by
        rcases kvEntry_grow c₀ ch log m with hk | ⟨cs, hk⟩
        · rw [hk]; exact h1
        · have hlen : log.length < l.length := by
            rcases Nat.lt_or_ge log.length l.length with h | h
            · exact h
            · exact absurd (h1.eq_of_length (Nat.le_antisymm h1.length_le h)) he
          have hk' : kvEntry c₀ ch log m <+: kvOf c₀ ch (kvEntry c₀ ch log m) D :=
            kvOf_extends _ _ _ _
          apply List.prefix_of_prefix_length_le hk' h2'
          rw [hk]; simp only [List.length_append, List.length_singleton]; omega
      obtain ⟨D', hD', hk⟩ := kvOf_ivt_aux c₀ ch l D (kvEntry c₀ ch log m) hstep h2'
      exact ⟨m :: D', List.cons_prefix_cons.2 ⟨rfl, hD'⟩, hk⟩

/-- **The intermediate value lemma**: a log between the models of `A₀` and of `B ⊒ A₀` (prefix
order) is the model of some `A` between them. Since each entry appends at most one revision, the
models of the prefixes between `A₀` and `B` pass through every log in between. -/
theorem kvOf_ivt (c₀ : w64) (ch : apply.Chain) (log₀ l : mvcc.Log) (A₀ B : List EntryModel)
    (hAB : A₀ <+: B) (h1 : kvOf c₀ ch log₀ A₀ <+: l) (h2 : l <+: kvOf c₀ ch log₀ B) :
    ∃ A, A₀ <+: A ∧ A <+: B ∧ kvOf c₀ ch log₀ A = l := by
  obtain ⟨D, rfl⟩ := hAB
  rw [kvOf_append] at h2
  obtain ⟨D', hD', hk⟩ := kvOf_ivt_aux c₀ ch l D _ h1 h2
  refine ⟨A₀ ++ D', List.prefix_append _ _, ?_, ?_⟩
  · obtain ⟨E, rfl⟩ := hD'
    rw [← List.append_assoc]; exact List.prefix_append _ _
  · rw [kvOf_append]; exact hk

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

/-- **The chain's relation on a plain request is the function, or an auth rejection.** -/
theorem chainStep_plain : ∀ (c : apply.Chain) (rq : apply.IRRModel) (log : mvcc.Log)
    (o : apply.Outcome), plainReq rq → apply.chainStep apply.backendStep c rq log o →
      o.logAfter log = chainLog c rq log ∨ o = .rejected .auth
  | .backend, rq, log, o, hp, h => Or.inl (backendStep_plain rq log o hp h)
  | .corrupt c, rq, log, o, hp, h => by
    simp only [apply.chainStep] at h
    simp only [chainLog]
    split at h
    · rename_i hk; rw [if_pos hk, h]; left; rfl
    · rename_i hk; rw [if_neg hk]; exact chainStep_plain c rq log o hp h
  | .capped c, rq, log, o, hp, h => by
    simp only [apply.chainStep] at h
    simp only [chainLog]
    split at h
    · rename_i hk; rw [if_pos hk, h]; left; rfl
    · rename_i hk
      rw [if_neg hk]
      split at h
      · rename_i ht
        unfold plainReq at hp; rw [ht] at hp; exact hp.elim
      · exact chainStep_plain c rq log o hp h
  | .auth c, rq, log, o, hp, h => by
    simp only [apply.chainStep] at h
    simp only [chainLog]
    split at h
    · rcases h with h | h
      · right; exact h
      · exact chainStep_plain c rq log o hp h
    · exact chainStep_plain c rq log o hp h
  | .quota c, rq, log, o, hp, h => by
    simp only [apply.chainStep] at h
    simp only [chainLog]
    split at h
    · obtain ⟨o', h1, h2⟩ := h
      rcases h2 with rfl | ⟨l, rfl, rfl⟩
      · exact chainStep_plain c rq log _ hp h1
      · rcases chainStep_plain c rq log _ hp h1 with h | h
        · left; simpa [apply.Outcome.logAfter] using h
        · cases h
    · exact chainStep_plain c rq log o hp h

/-- **`dispatch`'s relation on a plain request is the function, or an auth rejection.** -/
theorem dispatchStep_plain (c : apply.Chain) (rq : apply.IRRModel) (v3 : Bool) (log : mvcc.Log)
    (o : apply.Outcome) (hp : plainReq rq) (h : apply.dispatchStep c rq v3 log o) :
    o.logAfter log = dispatchLog c rq v3 log ∨ o = .rejected .auth := by
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
`dispatchLog` says, unless the outcome is an auth rejection (`.dispatched (.rejected .auth) _`, the
log unchanged). A skipped or admin-rejected request changes nothing, and `dispatchLog` agrees: a
plain request that `Apply` may skip or reject is no put and no delete, so `dispatchLog` changes
nothing for it either. -/
theorem applyStep_plain (rq : apply.IRRModel) (v3 : Bool) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (hp : plainReq rq) (h : apply.applyStep rq v3 x x' out) :
    x'.chain = x.chain ∧
      (x'.log = dispatchLog x.chain rq v3 x.log ∨
        ∃ skip, out = .dispatched (.rejected .auth) skip ∧ x'.log = x.log) := by
  have hnochg : (apply.noSideEffect rq = true ∨ apply.needAdminPermission rq = true) →
      dispatchLog x.chain rq v3 x.log = x.log := by
    intro hn
    unfold dispatchLog
    split
    · rfl
    · split
      · rename_i hs
        have hk : apply.dispatchKind rq ≠ .put ∧ apply.dispatchKind rq ≠ .deleteRange := by
          unfold plainReq at hp
          constructor
          · intro hk; rw [hk] at hp; rcases hn with hn | hn
            · rw [hp.1] at hn; cases hn
            · rw [hp.2.1] at hn; cases hn
          · intro hk; rw [hk] at hp; rcases hn with hn | hn
            · rw [hp.1] at hn; cases hn
            · rw [hp.2.1] at hn; cases hn
        -- a store kind other than put and delete that is plain: a range; it changes no log
        have hkr : ∀ c : apply.Chain, chainLog c rq x.log = x.log := by
          intro c
          induction c with
          | backend =>
            simp only [chainLog, backendLog]
            split
            · rename_i hk'; exact absurd hk' hk.1
            · rename_i hk'; exact absurd hk' hk.2
            · rfl
          | corrupt c ih => simp only [chainLog]; split <;> simp [ih]
          | capped c ih => simp only [chainLog]; split <;> simp [ih]
          | auth c ih => simp only [chainLog]; exact ih
          | quota c ih => simp only [chainLog]; exact ih
        exact hkr _
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
    rcases dispatchStep_plain x.chain rq v3 x.log o hp hd with h' | h'
    · left; rw [hl, h']
    · right; refine ⟨skip, by rw [h'], ?_⟩; rw [hl, h']; rfl

/-- **A raft entry's step on a plain entry**: the chain unchanged, and the log as `kvEntry` says,
unless the entry's request was rejected by the auth layer (the log unchanged). -/
theorem batchStep_plain (c₀ : w64) (m : EntryModel) (x x' : apply.ApplyKV)
    (hp : plainEntry m) (h : batchStep c₀ m x x') :
    x'.chain = x.chain ∧ (x'.log = kvEntry c₀ x.chain x.log m ∨ x'.log = x.log) := by
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
      exact ⟨rfl, Or.inl rfl⟩
    · rename_i hd
      rw [if_neg hd]
      obtain ⟨rq, id, hdec, -, h⟩ := h
      rw [hdec]
      obtain ⟨hc, h⟩ := applyStep_plain rq _ x x' out (hp ht hd rq hdec) h
      refine ⟨hc, ?_⟩
      rcases h with h | ⟨-, -, h⟩
      · left; exact h
      · right; exact h
  · rename_i ht
    rw [if_neg ht]
    subst h
    exact ⟨rfl, Or.inl rfl⟩

end EtcdGrove
end Perennial

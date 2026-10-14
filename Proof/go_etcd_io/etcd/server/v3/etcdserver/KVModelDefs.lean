/-
**The KV model of the committed raft log: the definitions** (unit T1, 2026-10-14; `notes/decisions.md`, "Put and Get
as persistent atomic updates linearized by raft"). Pure. Lean-first (no Rocq counterpart).

A persistent atomic update fires at **commit**, before any member applies the entry, so the KV
state after a committed log must be a function of the log. The apply package's model
(`apply.applyStep`, `apply.chainStep`) is a relation. This file gives the function, `kvRaftOf`, and
says exactly where the relation departs from it.

- **Plain requests** (`plainReq`): a put with lease `0` and no ignore flags, a range, a delete
  without `PrevKv`, or a request that does not touch the store. A put or delete must not also
  carry a field that makes `Apply` skip it (`noSideEffect`) or check admin permission
  (`needAdminPermission`). Excluded: txn, compaction, lease grant and revocation, alarm requests
  and `AuthEnable` (their outcomes, or the outcomes of later requests, depend on stores that the
  model treats as oracles).
- **The deterministic step** (`chainLog`, `dispatchLog`, `kvEntry`) and the fold `kvRaftOf c₀ ch log₀
  A` over raft entries: an empty entry, a conf change and an entry at or below the consistent
  index `c₀` change nothing.
- **Where the relation departs from it** (`applyStep_plain`, `batchStep_plain`): for a plain
  request, every outcome the relation allows changes the log as `dispatchLog` does, leaves the
  chain alone, or is an **auth rejection** (`.rejected .auth`, the log unchanged). The model
  allows the auth layer to reject whatever the store's state. Excluding that needs the auth
  layer's mode in the model (`authOn`, the next step: `notes/decisions.md`).
- **Shape** (`kvEntry_grow`, `kvRaftOf_prefix`) and the **intermediate value lemma** (`kvRaftOf_ivt`): a log
  between `kvRaftOf A₀` and `kvRaftOf B` (prefix order) is `kvRaftOf A` for some `A` between `A₀` and `B`,
  because each entry appends at most one revision.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftpb

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

/-- The log `L` after the applied index `ai₀`: consecutive indices from `ai₀ + 1`, no overflow,
normal entries and v1 conf changes. -/
def srvIdxOk (ai₀ : w64) (L : List EntryModel) : Prop :=
  uint.Z ai₀ + 1 + L.length < 2 ^ 64 ∧
  ∀ (n : Nat) (m : EntryModel), L[n]? = some m →
    uint.Z m.index = uint.Z ai₀ + 1 + n ∧
      (m.typ = W32 0 ∨ (m.typ = W32 1 ∧ isConfChangeEncoding m.data))

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
  | .auth _ c, rq, log => chainLog c rq log
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
def kvRaftOf (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) (A : List EntryModel) : mvcc.Log :=
  A.foldl (kvEntry c₀ ch) log₀

/-- **The value of `k`** in the state after `log`. -/
def kvVal (log : mvcc.Log) (k : GoString) : Option GoString :=
  (mvcc.findKey k (mvcc.stateAfter log)).map EtcdKv.value

theorem kvRaftOf_nil (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) : kvRaftOf c₀ ch log₀ [] = log₀ := rfl

theorem kvRaftOf_append (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) (A B : List EntryModel) :
    kvRaftOf c₀ ch log₀ (A ++ B) = kvRaftOf c₀ ch (kvRaftOf c₀ ch log₀ A) B := by
  unfold kvRaftOf; exact List.foldl_append

theorem kvRaftOf_snoc (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) (A : List EntryModel)
    (m : EntryModel) : kvRaftOf c₀ ch log₀ (A ++ [m]) = kvEntry c₀ ch (kvRaftOf c₀ ch log₀ A) m := by
  rw [kvRaftOf_append]; rfl

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
  | .auth _ c, rq, log => by simp only [chainLog]; exact chainLog_grow c rq log
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

theorem kvRaftOf_extends (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) (A : List EntryModel) :
    log₀ <+: kvRaftOf c₀ ch log₀ A := by
  induction A generalizing log₀ with
  | nil => exact List.prefix_refl _
  | cons m A ih =>
    show log₀ <+: kvRaftOf c₀ ch (kvEntry c₀ ch log₀ m) A
    exact (kvEntry_prefix c₀ ch log₀ m).trans (ih _)

/-- **The model grows with the raft log.** -/
theorem kvRaftOf_prefix (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) (A B : List EntryModel)
    (h : A <+: B) : kvRaftOf c₀ ch log₀ A <+: kvRaftOf c₀ ch log₀ B := by
  obtain ⟨D, rfl⟩ := h
  rw [kvRaftOf_append]
  exact kvRaftOf_extends _ _ _ _

/-- The intermediate value lemma, from a log: a log between `log` and the fold of `D` from it is
the fold of a prefix of `D`. -/
theorem kvRaftOf_ivt_aux (c₀ : w64) (ch : apply.Chain) (l : mvcc.Log) :
    ∀ (D : List EntryModel) (log : mvcc.Log), log <+: l → l <+: kvRaftOf c₀ ch log D →
      ∃ D', D' <+: D ∧ kvRaftOf c₀ ch log D' = l
  | [], log, h1, h2 => ⟨[], List.prefix_refl _, h1.eq_of_length (Nat.le_antisymm h1.length_le h2.length_le)⟩
  | m :: D, log, h1, h2 => by
    by_cases he : log = l
    · exact ⟨[], List.nil_prefix, he⟩
    · have h2' : l <+: kvRaftOf c₀ ch (kvEntry c₀ ch log m) D := h2
      have hstep : kvEntry c₀ ch log m <+: l := by
        rcases kvEntry_grow c₀ ch log m with hk | ⟨cs, hk⟩
        · rw [hk]; exact h1
        · have hlen : log.length < l.length := by
            rcases Nat.lt_or_ge log.length l.length with h | h
            · exact h
            · exact absurd (h1.eq_of_length (Nat.le_antisymm h1.length_le h)) he
          have hk' : kvEntry c₀ ch log m <+: kvRaftOf c₀ ch (kvEntry c₀ ch log m) D :=
            kvRaftOf_extends _ _ _ _
          apply List.prefix_of_prefix_length_le hk' h2'
          rw [hk]; simp only [List.length_append, List.length_singleton]; omega
      obtain ⟨D', hD', hk⟩ := kvRaftOf_ivt_aux c₀ ch l D (kvEntry c₀ ch log m) hstep h2'
      exact ⟨m :: D', List.cons_prefix_cons.2 ⟨rfl, hD'⟩, hk⟩

/-- **The intermediate value lemma**: a log between the models of `A₀` and of `B ⊒ A₀` (prefix
order) is the model of some `A` between them. Since each entry appends at most one revision, the
models of the prefixes between `A₀` and `B` pass through every log in between. -/
theorem kvRaftOf_ivt (c₀ : w64) (ch : apply.Chain) (log₀ l : mvcc.Log) (A₀ B : List EntryModel)
    (hAB : A₀ <+: B) (h1 : kvRaftOf c₀ ch log₀ A₀ <+: l) (h2 : l <+: kvRaftOf c₀ ch log₀ B) :
    ∃ A, A₀ <+: A ∧ A <+: B ∧ kvRaftOf c₀ ch log₀ A = l := by
  obtain ⟨D, rfl⟩ := hAB
  rw [kvRaftOf_append] at h2
  obtain ⟨D', hD', hk⟩ := kvRaftOf_ivt_aux c₀ ch l D _ h1 h2
  refine ⟨A₀ ++ D', List.prefix_append _ _, ?_, ?_⟩
  · obtain ⟨E, rfl⟩ := hD'
    rw [← List.append_assoc]; exact List.prefix_append _ _
  · rw [kvRaftOf_append]; exact hk


/-! ## A plain put's and a write-free request's effect on the values -/

section putValues
open mvcc

/-- The put of `k` finds the value it wrote. -/
theorem kvVal_putKv (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) (r : w64)
    (k v : GoString) (l : w64) : (findKey k (putKv r k v l s)).map EtcdKv.value = some v := by
  unfold putKv
  simp only
  rw [findKey_btInsert _ s hs]
  cases h : s.find? (fun v => decide (v.key = k)) with
  | none => simp
  | some kv =>
    have hk : kv.key = k := by simpa using List.find?_some h
    simp [hk]

/-- **A put's change writes its value** (no `IgnoreValue`). -/
theorem kvVal_put (log : Log) (op : OpFull) (pv : Option EtcdKv) (hiv : op.ignoreValue = false) :
    kvVal (log ++ [[txn.putChangeOf op pv]]) op.key = some op.val := by
  unfold kvVal
  rw [stateAfter_append]
  simp only [applyChanges, List.foldl_cons, List.foldl_nil, txn.putChangeOf, applyChange]
  rw [kvVal_putKv _ (stateAfter_sorted _)]
  simp [txn.putValOf, hiv]

/-- **A put's change leaves the other keys.** -/
theorem kvVal_put_other (log : Log) (op : OpFull) (pv : Option EtcdKv) (k : GoString)
    (hne : op.key ≠ k) :
    kvVal (log ++ [[txn.putChangeOf op pv]]) k = kvVal log k := by
  unfold kvVal
  rw [stateAfter_append]
  simp only [applyChanges, List.foldl_cons, List.foldl_nil, txn.putChangeOf, applyChange]
  rw [findKey_putKv_other (stateAfter_sorted _) _ _ _ _ _ hne]

end putValues

/-- A request that is neither a put nor a delete changes no log through any chain. -/
theorem chainLog_nonwrite (rq : apply.IRRModel) (log : mvcc.Log)
    (hk : apply.dispatchKind rq ≠ .put ∧ apply.dispatchKind rq ≠ .deleteRange) :
    ∀ c : apply.Chain, chainLog c rq log = log := by
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
  | auth _ c ih => simp only [chainLog]; exact ih
  | quota c ih => simp only [chainLog]; exact ih

/-- **A write-free entry keeps the model** (an empty entry, a conf change, or a request that is
neither a put nor a delete). -/
theorem kvEntry_nonwrite (c₀ : w64) (ch : apply.Chain) (log : mvcc.Log) (e : EntryModel)
    (h : e.data = [] ∨ e.typ ≠ W32 0 ∨ ∀ rq, apply.irrDecode e.data = some rq →
      apply.dispatchKind rq ≠ .put ∧ apply.dispatchKind rq ≠ .deleteRange) :
    kvEntry c₀ ch log e = log := by
  unfold kvEntry
  split
  · rename_i ht
    split
    · rfl
    · rename_i hd
      split
      · rename_i rq hdec
        rcases h with h | h | h
        · exact absurd h hd
        · exact absurd ht h
        · unfold dispatchLog
          split
          · rfl
          · split
            · exact chainLog_nonwrite rq log (h rq hdec) ch
            · rfl
      · rfl
  · rfl

/-- **A plain put entry above the consistent index, through the base chain with auth off**:
the put's change. -/
theorem kvEntry_put (c₀ : w64) (log : mvcc.Log) (e : EntryModel) (rq : apply.IRRModel)
    (op : OpFull) (ht : e.typ = W32 0) (hd : e.data ≠ []) (hdec : apply.irrDecode e.data = some rq)
    (hk : apply.dispatchKind rq = .put) (hop : rq.put = some op)
    (hidx : uint.Z c₀ < uint.Z e.index) :
    kvEntry c₀ (apply.alarmChain false false false) log e =
      log ++ [[txn.putChangeOf op (mvcc.findKey op.key (mvcc.stateAfter log))]] := by
  unfold kvEntry
  rw [if_pos ht, if_neg hd, hdec]
  simp only
  unfold dispatchLog
  have h1 : apply.preV3Kind (apply.dispatchKind rq) = false := by rw [hk]; rfl
  have h2 : apply.storeKind (apply.dispatchKind rq) = true := by rw [hk]; rfl
  simp only [h1, h2, decide_eq_true hidx, Bool.false_eq_true, false_or, ↓reduceIte, reduceCtorEq]
  simp only [apply.alarmChain, apply.baseChain, Bool.false_eq_true, ↓reduceIte, chainLog,
    backendLog, hk, hop]

end EtcdGrove
end Perennial

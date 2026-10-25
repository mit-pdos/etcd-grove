/-
**The KV model of the committed raft log: the definitions** (unit T1, 2026-10-14; unit T2,
2026-10-15: every KV operation; `notes/decisions.md`, "Put and Get as persistent atomic updates
linearized by raft" and "Every KV operation as a persistent atomic update on the whole state").
Pure. Lean-first (no Rocq counterpart).

A persistent atomic update fires at **commit**, before any member applies the entry, so the KV
state after a committed log must be a function of the log. The apply package's model
(`apply.applyStep`, `apply.chainStep`) is a relation. This file gives the function, `kvRaftOf`, and
says exactly where the relation departs from it.

- **Plain requests** (`plainReq`): a put with lease `0` (any other flags), a range, a delete, a
  plain transaction (`txn.txnPlain`: gets at revision `0`, puts with lease `0` and no
  `IgnoreLease`), or a request that does not touch the store (2026-10-15, unit T2; T1 had puts
  without ignore flags and deletes without `PrevKv` only). A put, delete or transaction must not
  also carry a field that makes `Apply` skip it (`noSideEffect`) or check admin permission
  (`needAdminPermission`). Excluded: compaction, lease grant and revocation, alarm requests and
  `AuthEnable` (their outcomes, or the outcomes of later requests, depend on stores that the model
  treats as oracles), and a put or transaction naming a lease (the lessor's lookup). D19k
  (2026-10-18): narrowed to the kinds the verified proposers send, the KV writes and the
  monitors' `ClusterMemberAttrSet`/`ClusterVersionSet` (no range, no auth or other request whose
  answer's error the apply package leaves open), none with an auth field set. D19q (2026-10-18):
  that set is now `plainCover`, what the generic proofs cover; `plainReq` is it at the kinds the
  verified proposers send (`putgetKind`; D44, 2026-10-25: no workload parameter, D19q's
  `SrvWorkload`, any more).
- **The deterministic step** (`chainLog`, `dispatchLog`, `kvEntry`) and the fold `kvRaftOf c₀ ch log₀
  A` over raft entries: an empty entry, a conf change and an entry at or below the consistent
  index `c₀` change nothing.
- **Where the relation departs from it** (`applyStep_plain`, `batchStep_plain`, `KVModel.lean`):
  for a plain request, every outcome the relation allows changes the log as `dispatchLog` does
  and leaves the chain alone, unless the chain is not `kvExact` (an enabled auth layer's
  rejection, a capped layer's), the log unchanged. The start's chain is `kvExact`.
- **The state** (`KVState`, `kvStateOf`: the store at its latest revision; 2026-10-15, unit T2)
  and **an operation's step on it** (`KVOp`, `kvOpStep`, `reqKVOp`, `kvReqStep`): the backend's
  log follows the state (`kvStateOf_backendLog`), so the KV ghost state can be the state.
- **Shape** (`kvEntry_grow`, `kvRaftOf_prefix`) and the **intermediate value lemma** (`kvRaftOf_ivt`): a log
  between `kvRaftOf A₀` and `kvRaftOf B` (prefix order) is `kvRaftOf A` for some `A` between `A₀` and `B`,
  because each entry appends at most one revision.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.InvUber
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftpb
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.etcd.server.v3.etcdserver

/-! ## Plain requests and entries -/

/-- **The requests the generic proofs cover** (the KV model below, `KVModel.lean`; the dead
NOSPACE branch, `NoSpaceDead.lean`; the shapes, `WorkloadDefs.lean`): until the workload
parameter (D19q, 2026-10-18) this was `plainReq` itself. 2026-10-15 (unit T2): a put with any
flags but a lease, any delete, a plain transaction (`txn.txnPlain`: its gets at revision `0`, its
puts with no lease and no `IgnoreLease`). D19k (2026-10-18): only the kinds the verified proposers
send (the KV writes, the monitors' member attributes and cluster version), none with an auth
field set (`needAdminPermission`); every other kind was `True` and its answer's error unknown,
which kept `applyEntryNormal`'s NOSPACE branch reachable in the model. D22 (2026-10-23): a
cluster request has no side-effect-free field set either (`noSideEffect`: with one, `Apply` skips
it on a member where no one waits for it, so the rest buckets would depend on where the request
was proposed). A workload admitting
more (a lease-enabled one: `LeaseGrant`, `LeaseRevoke`) extends this predicate and the generic
proofs over it. -/
def plainCover (rq : apply.IRRModel) : Prop :=
  match apply.dispatchKind rq with
  | .put => apply.noSideEffect rq = false ∧ apply.needAdminPermission rq = false ∧
      ∀ op, rq.put = some op → op.leaseID = W64 0
  | .deleteRange => apply.noSideEffect rq = false ∧ apply.needAdminPermission rq = false
  | .txn => apply.noSideEffect rq = false ∧ apply.needAdminPermission rq = false ∧
      ∀ t, rq.txn = some t → txn.txnPlain t
  | .clusterVersionSet | .clusterMemberAttrSet =>
      apply.noSideEffect rq = false ∧ apply.needAdminPermission rq = false
  | _ => False

/-- **A KV operation** as the server applies it. -/
inductive KVOp where
  | put (o : OpFull)
  | range (o : OpFull)
  | deleteRange (o : OpFull)
  | txn (t : TxnModel)

/-- **The KV operation of a request**, by `dispatch`'s kind. -/
def reqKVOp (rq : apply.IRRModel) : Option KVOp :=
  match apply.dispatchKind rq with
  | .put => rq.put.map .put
  | .range => rq.range.map .range
  | .deleteRange => rq.deleteRange.map .deleteRange
  | .txn => rq.txn.map .txn
  | _ => none

/-- **The kinds the server's verified proposers send**: the KV writes and the monitors' requests
(D44, 2026-10-25: a fact of the proposers, not a parameter; until then D19q's workload record,
`SrvWorkload`, whose one instance admitted exactly these). -/
def putgetKind (k : apply.ReqKind) : Prop :=
  k = .put ∨ k = .deleteRange ∨ k = .txn ∨ k = .clusterMemberAttrSet ∨ k = .clusterVersionSet

/-- **A plain request**: covered by the generic proofs (`plainCover`, the D19k narrowing), of a
kind the server's verified proposers send (`putgetKind`). -/
def plainReq (rq : apply.IRRModel) : Prop :=
  plainCover rq ∧ putgetKind (apply.dispatchKind rq)

/-- A request's kind does not depend on the header the server stamps. -/
theorem putgetKind_header (rq : apply.IRRModel) (hm : apply.HeaderModel)
    (h : putgetKind (apply.dispatchKind rq)) :
    putgetKind (apply.dispatchKind { rq with header := some hm }) := by
  simpa [apply.dispatchKind] using h

/-- A KV write's kind is a proposer's. -/
theorem putgetKind_kv (rq : apply.IRRModel) (h : apply.dispatchKind rq = .put ∨
    apply.dispatchKind rq = .deleteRange ∨ apply.dispatchKind rq = .txn) :
    putgetKind (apply.dispatchKind rq) := by
  unfold putgetKind; rcases h with h | h | h <;> simp [h]

/-- A monitor's request's kind is a proposer's. -/
theorem putgetKind_cluster (rq : apply.IRRModel) (h : apply.dispatchKind rq = .clusterMemberAttrSet ∨
    apply.dispatchKind rq = .clusterVersionSet) : putgetKind (apply.dispatchKind rq) := by
  unfold putgetKind; rcases h with h | h <;> simp [h]

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

/-- The log `L` after the applied index `ai₀`, entry by entry (2026-10-16, stage R7b: what raft's
commit step establishes, `srvIdxOk` without its overflow bound): consecutive indices from
`ai₀ + 1`, normal entries and v1 conf changes. -/
abbrev srvIdxOkW [FfiSyntax] (ai₀ : w64) (L : List EntryModel) : Prop :=
  ∀ (n : Nat) (m : EntryModel), L[n]? = some m →
    uint.Z m.index = uint.Z ai₀ + 1 + n ∧
      (m.typ = W32 0 ∨ (m.typ = W32 1 ∧ isConfChangeEncoding m.data))

/-- The log `L` after the applied index `ai₀`: consecutive indices from `ai₀ + 1`, no overflow,
normal entries and v1 conf changes. (The overflow bound is on the *next* index, `ai₀ + 1 + |L|`,
which raft's commit step cannot promise: the KV invariant keeps `srvIdxOkW`, and the bound comes
with a `Ready`'s batch, a premise on the run, `rnLogFits`; 2026-10-16, stage R7b.) -/
def srvIdxOk [FfiSyntax] (ai₀ : w64) (L : List EntryModel) : Prop :=
  uint.Z ai₀ + 1 + L.length < 2 ^ 64 ∧ srvIdxOkW ai₀ L

/-- A prefix of a consecutive log is consecutive. -/
theorem srvIdxOkW_prefix [FfiSyntax] (ai₀ : w64) (A B : List EntryModel) (h : srvIdxOkW ai₀ B) (hp : A <+: B) :
    srvIdxOkW ai₀ A := by
  intro n m hm
  obtain ⟨r, rfl⟩ := hp
  exact h n m (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hm).1]; exact hm)

/-- **One entry on** (2026-10-16, stage R7b: what a firing of the server's update gives): the
entry at the next index, normal or a v1 conf change. -/
theorem srvIdxOkW_snoc [FfiSyntax] (ai₀ : w64) (L : List EntryModel) (e : EntryModel) (h : srvIdxOkW ai₀ L)
    (hidx : uint.Z e.index = uint.Z ai₀ + 1 + L.length)
    (hty : e.typ = W32 0 ∨ (e.typ = W32 1 ∧ isConfChangeEncoding e.data)) :
    srvIdxOkW ai₀ (L ++ [e]) := by
  intro n m hm
  rcases Nat.lt_or_ge n L.length with hn | hn
  · rw [List.getElem?_append_left hn] at hm
    exact h n m hm
  · rw [List.getElem?_append_right hn] at hm
    have hn' : n = L.length := by
      have := (List.getElem?_eq_some_iff.mp hm).1
      simp only [List.length_singleton] at this
      omega
    subst hn'
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hm
    subst hm
    exact ⟨hidx, hty⟩

/-- `srvIdxOk` from the entry-wise facts and the bound. -/
theorem srvIdxOk_of_W [FfiSyntax] (ai₀ : w64) (L : List EntryModel) (h : srvIdxOkW ai₀ L)
    (hb : uint.Z ai₀ + 1 + L.length < 2 ^ 64) : srvIdxOk ai₀ L := ⟨hb, h⟩

/-! ## The deterministic step -/

open Classical in
/-- **The backend's effect on the log**, deterministically (`apply.backendStep`'s outcome for a
plain request): a put not finding the previous key-value an ignore flag needs is rejected, else
its change appended; a delete commits its range's deletions; a transaction whose path does not
find a previous key-value it needs is rejected (`checkTxn`), else the server's run committed. -/
def backendLog (rq : apply.IRRModel) (log : mvcc.Log) : mvcc.Log :=
  match apply.dispatchKind rq with
  | .put =>
      match rq.put with
      | some op =>
        if txn.needsPrev op && (mvcc.findKey op.key (mvcc.stateAfter log)).isNone then log
        else log ++ [[txn.putChangeOf op (mvcc.findKey op.key (mvcc.stateAfter log))]]
      | none => log
  | .deleteRange =>
      match rq.deleteRange with
      | some op => mvcc.commitLog log (txn.delChanges (mvcc.stateAfter log) op)
      | none => log
  | .txn =>
      match rq.txn with
      | some t =>
        if txn.PathsIgnOk (mvcc.stateAfter log) (t.branch (txn.txnOk (mvcc.stateAfter log) t)) then
          mvcc.commitLog log (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1
        else log
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

theorem commitLog_grow (log : mvcc.Log) (pend : List mvcc.Change) :
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
    · split
      · left; rfl
      · right; exact ⟨_, rfl⟩
    · left; rfl
  · split
    · exact commitLog_grow _ _
    · left; rfl
  · split
    · split
      · exact commitLog_grow _ _
      · left; rfl
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


/-! ## A plain put's and a write-free request's effect on the values -/

section putValues
open mvcc

end putValues

/-- **A write kind**: a put, a delete or a transaction (2026-10-15, unit T2: a transaction too). -/
def writeKind (k : apply.ReqKind) : Prop := k = .put ∨ k = .deleteRange ∨ k = .txn

/-- A request that is no put, no delete and no transaction changes no log through any chain. -/
theorem chainLog_nonwrite (rq : apply.IRRModel) (log : mvcc.Log)
    (hk : ¬ writeKind (apply.dispatchKind rq)) :
    ∀ c : apply.Chain, chainLog c rq log = log := by
  intro c
  unfold writeKind at hk
  induction c with
  | backend =>
    simp only [chainLog, backendLog]
    split
    · rename_i hk'; exact absurd (Or.inl hk') hk
    · rename_i hk'; exact absurd (Or.inr (Or.inl hk')) hk
    · rename_i hk'; exact absurd (Or.inr (Or.inr hk')) hk
    · rfl
  | corrupt c ih => simp only [chainLog]; split <;> simp [ih]
  | capped c ih => simp only [chainLog]; split <;> simp [ih]
  | auth _ c ih => simp only [chainLog]; exact ih
  | quota c ih => simp only [chainLog]; exact ih

/-- **A write-free entry keeps the model** (an empty entry, a conf change, or a request that is
no put, no delete and no transaction). -/
theorem kvEntry_nonwrite (c₀ : w64) (ch : apply.Chain) (log : mvcc.Log) (e : EntryModel)
    (h : e.data = [] ∨ e.typ ≠ W32 0 ∨ ∀ rq, apply.irrDecode e.data = some rq →
      ¬ writeKind (apply.dispatchKind rq)) :
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

/-- **`dispatch` through the base chain, with `v3`, is the backend's** (whatever the kind: the
pre-v3 kinds and the kinds the chain does not run change no log, as the backend's model). -/
theorem dispatchLog_base (rq : apply.IRRModel) (log : mvcc.Log) :
    dispatchLog (apply.alarmChain false false false) rq true log = backendLog rq log := by
  have hb : chainLog (apply.alarmChain false false false) rq log = backendLog rq log := by
    simp only [apply.alarmChain, apply.baseChain, Bool.false_eq_true, ↓reduceIte, chainLog]
  have hnw : ¬ writeKind (apply.dispatchKind rq) → backendLog rq log = log := by
    intro hk
    have := chainLog_nonwrite rq log hk .backend
    simpa only [chainLog] using this
  unfold dispatchLog
  rw [hb]
  split
  · rename_i h
    rcases h with h | h
    · rw [hnw]
      unfold writeKind
      intro hk; rcases hk with hk | hk | hk <;> rw [hk] at h <;> cases h
    · cases h
  · split
    · rfl
    · rename_i _ h
      rw [hnw]
      unfold writeKind
      intro hk; rcases hk with hk | hk | hk <;> rw [hk] at h <;> exact h rfl

/-- **An entry above the consistent index, through the base chain**: its request's backend log
(2026-10-15, unit T2; it was `kvEntry_put`, for a put). -/
theorem kvEntry_base (c₀ : w64) (log : mvcc.Log) (e : EntryModel) (rq : apply.IRRModel)
    (ht : e.typ = W32 0) (hd : e.data ≠ []) (hdec : apply.irrDecode e.data = some rq)
    (hidx : uint.Z c₀ < uint.Z e.index) :
    kvEntry c₀ (apply.alarmChain false false false) log e = backendLog rq log := by
  unfold kvEntry
  rw [if_pos ht, if_neg hd, hdec]
  simp only
  rw [decide_eq_true hidx]
  exact dispatchLog_base rq log

/-! ## etcd's KV state, at every revision it keeps (D46, 2026-10-25; D45 kept a store per revision)

The abstract state of etcd's KV as its clients see it (`KVState`), as etcd's mvcc keeps it: the
store at the compaction revision (`base`, a finite map from keys to their records, `KVStore`,
`KVStore.lean`) and, for each later revision, its changes in order (`later`; mvcc's key bucket
records each change at its own revision `(main, sub)`, and a watch's events are those records:
`watchableStoreTxnWrite.End`, `kvsToEvents`). The store at a revision is computed from them
(`KVState.at`: the changes applied in order from the base, as `mvcc.stateAt` does). A write adds
the next revision's changes (`KVState.commit`); a compaction would raise `compacted` and fold the
dropped revisions into `base` (not in the server's model yet: the server's state has
`compacted = 0`). The current store's key-values sorted by key (`σ.kvs`) are what the range
semantics read (`txn.srvRangeOk`, `mvcc.findKey`, ...). A log's state is `kvStateOf` (its first
revision's store, then its later revisions' changes); an operation's effect on it is `kvOpStep` (a
read's the identity, a rejected request's too), a function of the state, which the backend's log
follows (`kvStateOf_backendLog`). -/

/-- **etcd's KV at every revision it keeps** (see the section header). -/
structure KVState where
  /-- the compaction revision: the earliest revision the state keeps -/
  compacted : Nat
  /-- the store at revision `compacted` -/
  base : KVStore
  /-- the changes of revisions `compacted + 1`, ..., the current one, each revision's in order -/
  later : List (List mvcc.Change)

/-- **The key-values after the revisions `l`**, applied in order from `s`, the first of them
revision `r0 + 1` (`mvcc.stateAfter`'s step: each revision's changes at its own revision). -/
def runFrom (r0 : Nat) (s : List EtcdKv) : List (List mvcc.Change) → List EtcdKv
  | [] => s
  | cs :: l => runFrom (r0 + 1) (mvcc.applyChanges (W64 ((r0 + 1 : Nat) : Int)) s cs) l

/-- **The current revision.** -/
def KVState.rev (σ : KVState) : Nat := σ.compacted + σ.later.length

/-- **The store at revision `r`** (one of `compacted`, ..., `rev`; empty below `compacted`, the
current store above `rev`): the base with the changes of the revisions up to `r`. -/
def KVState.at (σ : KVState) (r : Nat) : KVStore :=
  if r < σ.compacted then ∅
  else storeOf (runFrom σ.compacted σ.base.kvs (σ.later.take (r - σ.compacted)))

/-- **The changes of revision `r`** (one of `compacted + 1`, ..., `rev`; none outside), in order. -/
def KVState.changesAt (σ : KVState) (r : Nat) : List mvcc.Change :=
  if r ≤ σ.compacted then [] else (σ.later[r - σ.compacted - 1]?).getD []

/-- **The store at the current revision.** -/
def KVState.store (σ : KVState) : KVStore := σ.at σ.rev

/-- **The current store's key-values, sorted by key** (what the range semantics read). -/
def KVState.kvs (σ : KVState) : List EtcdKv := σ.store.kvs

/-- **The revision a range reads in the state `σ`**: the one asked, or (`rev ≤ 0`) the current. -/
def KVState.readRev (σ : KVState) (rev : w64) : Nat :=
  if sint.Z rev ≤ 0 then σ.rev else sint.nat rev

/-- The store at the current revision is the current store. -/
theorem KVState.at_rev (σ : KVState) : σ.at σ.rev = σ.store := rfl

theorem runFrom_sorted (r0 : Nat) (l : List (List mvcc.Change)) :
    ∀ {s : List EtcdKv}, s.Pairwise etcdKvLess → (runFrom r0 s l).Pairwise etcdKvLess := by
  induction l generalizing r0 with
  | nil => intro s hs; exact hs
  | cons cs l ih => intro s hs; exact ih (r0 + 1) (mvcc.applyChanges_sorted _ cs hs)

theorem runFrom_append (r0 : Nat) (s : List EtcdKv) (l : List (List mvcc.Change))
    (cs : List mvcc.Change) :
    runFrom r0 s (l ++ [cs]) =
      mvcc.applyChanges (W64 ((r0 + l.length + 1 : Nat) : Int)) (runFrom r0 s l) cs := by
  induction l generalizing r0 s with
  | nil => rfl
  | cons c l ih =>
    simp only [List.cons_append, runFrom, ih, List.length_cons]
    congr 3
    omega

/-- The key-values of the store at `r` are the changes up to `r` applied to the base's. -/
theorem KVState.at_kvs (σ : KVState) (r : Nat) (hr : σ.compacted ≤ r) :
    (σ.at r).kvs = runFrom σ.compacted σ.base.kvs (σ.later.take (r - σ.compacted)) := by
  unfold KVState.at
  rw [if_neg (by omega), kvs_storeOf _ (runFrom_sorted _ _ (KVStore.kvs_sorted _))]

theorem KVState.kvs_eq (σ : KVState) : σ.kvs = runFrom σ.compacted σ.base.kvs σ.later := by
  unfold KVState.kvs KVState.store
  rw [KVState.at_kvs σ σ.rev (by unfold KVState.rev; omega),
    List.take_of_length_le (by unfold KVState.rev; omega)]

/-- **The state of a log**: its first revision's store, then each later revision's changes, none
compacted; its current revision the log's last (`log.length - 1`: a read at `log` answers it). -/
def kvStateOf (l : mvcc.Log) : KVState :=
  ⟨0, storeOf (mvcc.stateAt l 0), l.drop 1⟩

/-- A write's commit of the changes `cs` at the next revision (none if it changed nothing:
`mvcc.commitLog`'s). -/
def KVState.commit (σ : KVState) (cs : List mvcc.Change) : KVState :=
  if cs = [] then σ else { σ with later := σ.later ++ [cs] }

theorem KVState.kvs_sorted (σ : KVState) : σ.kvs.Pairwise etcdKvLess := KVStore.kvs_sorted _

theorem kvStateOf_rev (l : mvcc.Log) : (kvStateOf l).rev = l.length - 1 := by
  simp [kvStateOf, KVState.rev]

theorem kvStateOf_compacted (l : mvcc.Log) : (kvStateOf l).compacted = 0 := rfl

/-- The log's states, revision by revision from `i`, are the changes of its later revisions
applied in order. -/
theorem runFrom_stateAt (l : mvcc.Log) :
    ∀ (k i : Nat), i + k ≤ l.length - 1 →
      runFrom i (mvcc.stateAt l i) ((l.drop (i + 1)).take k) = mvcc.stateAt l (i + k)
  | 0, i, _ => by simp [runFrom]
  | k + 1, i, h => by
    have hi : i + 1 < l.length := by omega
    rw [List.drop_eq_getElem_cons hi, List.take_succ_cons]
    simp only [runFrom]
    have hs : mvcc.stateAt l (i + 1) =
        mvcc.applyChanges (W64 ((i + 1 : Nat) : Int)) (mvcc.stateAt l i) l[i + 1] := by
      unfold mvcc.stateAt
      rw [List.take_add_one (i := i + 1), List.getElem?_eq_getElem hi, Option.toList_some,
        mvcc.stateAfter_append, List.length_take, Nat.min_eq_left (by omega)]
    rw [← hs, runFrom_stateAt l k (i + 1) (by omega)]
    congr 1
    omega

/-- The store at revision `r` of a log's state (`r` at most its last). -/
theorem kvStateOf_at (l : mvcc.Log) (r : Nat) (hr : r ≤ l.length - 1) :
    (kvStateOf l).at r = storeOf (mvcc.stateAt l r) := by
  unfold kvStateOf KVState.at
  simp only [Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  rw [kvs_storeOf _ (mvcc.stateAt_sorted l 0)]
  have := runFrom_stateAt l r 0 (by omega)
  simp only [Nat.zero_add] at this
  rw [this]

/-- Revision `r`'s key-values of a log's state are the log's state at `r`. -/
theorem kvStateOf_at_kvs (l : mvcc.Log) (r : Nat) (hr : r ≤ l.length - 1) :
    ((kvStateOf l).at r).kvs = mvcc.stateAt l r := by
  rw [kvStateOf_at l r hr, kvs_storeOf _ (mvcc.stateAt_sorted l r)]

theorem kvStateOf_store (l : mvcc.Log) : (kvStateOf l).store = storeOf (mvcc.stateAfter l) := by
  unfold KVState.store
  rw [kvStateOf_rev, kvStateOf_at l _ (Nat.le_refl _), mvcc.stateAt_last]

theorem kvStateOf_kvs (l : mvcc.Log) : (kvStateOf l).kvs = mvcc.stateAfter l := by
  unfold KVState.kvs
  rw [kvStateOf_store, kvs_storeOf _ (mvcc.stateAfter_sorted l)]

/-- Revision `r`'s changes in a log's state are the log's (`r` a later revision). -/
theorem kvStateOf_changesAt (l : mvcc.Log) (r : Nat) (h0 : 0 < r) :
    (kvStateOf l).changesAt r = l.getD r [] := by
  unfold kvStateOf KVState.changesAt
  simp only
  rw [if_neg (by omega), List.getElem?_drop, List.getD_eq_getElem?_getD]
  congr 2
  omega

theorem KVState.commit_nil (σ : KVState) : σ.commit [] = σ := by
  simp [KVState.commit]

theorem KVState.commit_rev (σ : KVState) (cs : List mvcc.Change) (h : cs ≠ []) :
    (σ.commit cs).rev = σ.rev + 1 := by
  simp only [KVState.commit, h, ↓reduceIte, KVState.rev, List.length_append, List.length_singleton]
  omega

theorem KVState.commit_kvs (σ : KVState) (cs : List mvcc.Change) (h : cs ≠ []) :
    (σ.commit cs).kvs = mvcc.applyChanges (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs cs := by
  rw [KVState.kvs_eq, KVState.kvs_eq]
  simp only [KVState.commit, h, ↓reduceIte]
  rw [runFrom_append]
  rfl

theorem KVState.commit_store (σ : KVState) (cs : List mvcc.Change) (h : cs ≠ []) :
    (σ.commit cs).store = storeOf (mvcc.applyChanges (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs cs) := by
  rw [← KVState.commit_kvs σ cs h, KVState.kvs, storeOf_kvs]

theorem KVState.commit_compacted (σ : KVState) (cs : List mvcc.Change) :
    (σ.commit cs).compacted = σ.compacted := by
  unfold KVState.commit; split <;> rfl

/-- A commit keeps the earlier revisions. -/
theorem KVState.commit_at (σ : KVState) (cs : List mvcc.Change) (r : Nat) (hr : r ≤ σ.rev) :
    (σ.commit cs).at r = σ.at r := by
  unfold KVState.commit
  split
  · rfl
  · unfold KVState.at
    simp only
    split
    · rfl
    · have : r - σ.compacted ≤ σ.later.length := by unfold KVState.rev at hr; omega
      rw [List.take_append_of_le_length this]

/-- A commit keeps the earlier revisions' changes. -/
theorem KVState.commit_changesAt (σ : KVState) (cs : List mvcc.Change) (r : Nat) (hr : r ≤ σ.rev) :
    (σ.commit cs).changesAt r = σ.changesAt r := by
  unfold KVState.commit
  split
  · rfl
  · unfold KVState.changesAt
    simp only
    split
    · rfl
    · have : r - σ.compacted - 1 < σ.later.length := by unfold KVState.rev at hr; omega
      rw [List.getElem?_append_left this]

open Classical in
/-- **The operation's effect on the state**: a put not finding the previous key-value its
ignore flag needs changes nothing, else commits its one change; a range changes nothing; a
delete commits its range's deletions; a transaction whose path does not find a previous
key-value it needs changes nothing (`checkTxn`'s error), else commits the server's run
(`srvRunTxn`, nested branches by their verdicts at the state). -/
def kvOpStep : KVOp → KVState → KVState
  | .put o, σ =>
    if txn.needsPrev o && (mvcc.findKey o.key σ.kvs).isNone then σ
    else σ.commit [txn.putChangeOf o (mvcc.findKey o.key σ.kvs)]
  | .range _, σ => σ
  | .deleteRange o, σ => σ.commit (txn.delChanges σ.kvs o)
  | .txn t, σ =>
    if txn.PathsIgnOk σ.kvs (t.branch (txn.txnOk σ.kvs t)) then
      σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.1
    else σ

/-- **A request's effect on the state**: its operation's, or none. -/
def kvReqStep (rq : apply.IRRModel) (σ : KVState) : KVState :=
  match reqKVOp rq with
  | some op => kvOpStep op σ
  | none => σ

theorem kvStateOf_commitLog (l : mvcc.Log) (cs : List mvcc.Change) (hl : l ≠ []) :
    kvStateOf (mvcc.commitLog l cs) = (kvStateOf l).commit cs := by
  have hpos := List.length_pos_iff.2 hl
  unfold mvcc.commitLog
  by_cases hc : cs = []
  · simp [hc, KVState.commit_nil]
  rw [if_neg hc]
  unfold KVState.commit kvStateOf
  rw [if_neg hc, mvcc.stateAt_append_lt _ _ hpos, List.drop_append_of_le_length (by omega)]

/-- **The backend's log follows the state**: the state after a request's backend log is the
request's step on the state before (a log with a revision: the server's always has two). -/
theorem kvStateOf_backendLog (rq : apply.IRRModel) (l : mvcc.Log) (hl : l ≠ []) :
    kvStateOf (backendLog rq l) = kvReqStep rq (kvStateOf l) := by
  have hpos := List.length_pos_iff.2 hl
  have hrev : (kvStateOf l).rev + 1 = l.length := by rw [kvStateOf_rev]; omega
  have hs : (kvStateOf l).kvs = mvcc.stateAfter l := kvStateOf_kvs l
  unfold backendLog kvReqStep reqKVOp
  cases hk : apply.dispatchKind rq
  case put =>
    dsimp only
    cases hp : rq.put with
    | none => rfl
    | some op =>
      simp only [Option.map_some, kvOpStep]
      rw [hs]
      split
      · rfl
      · have : l ++ [[txn.putChangeOf op (mvcc.findKey op.key (mvcc.stateAfter l))]] =
            mvcc.commitLog l [txn.putChangeOf op (mvcc.findKey op.key (mvcc.stateAfter l))] := by
          simp [mvcc.commitLog]
        rw [this, kvStateOf_commitLog _ _ hl]
  case range =>
    dsimp only
    cases hp : rq.range with
    | none => rfl
    | some o => rfl
  case deleteRange =>
    dsimp only
    cases hp : rq.deleteRange with
    | none => rfl
    | some op =>
      simp only [Option.map_some, kvOpStep]
      rw [kvStateOf_commitLog _ _ hl, hs]
  case txn =>
    dsimp only
    cases hp : rq.txn with
    | none => rfl
    | some t =>
      simp only [Option.map_some, kvOpStep]
      rw [hs, hrev]
      split
      · rw [kvStateOf_commitLog _ _ hl]
      · rfl
  all_goals rfl

end EtcdGrove
end Perennial

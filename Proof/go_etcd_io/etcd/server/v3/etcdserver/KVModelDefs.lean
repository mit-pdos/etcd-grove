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

/-! ## The state at the latest revision (2026-10-15, unit T2)

`notes/decisions.md`, "Every KV operation as a persistent atomic update on the whole state". The
abstract state of etcd's KV is the store at its latest revision (`KVState`): every key's
key-value (its value, create and mod revisions, version, lease: `EtcdKv`) and the current
revision. A log's state is `kvStateOf`; an operation's effect on it is `kvOpStep` (a read's the
identity, a rejected request's too), a function of the state, which the backend's log follows
(`kvStateOf_backendLog`). -/

/-- **The store at its latest revision**: the key-values (sorted by key) and the current
revision. -/
structure KVState where
  kvs : List EtcdKv
  rev : Nat

/-- **The state of a log**: after every revision, at its last revision (`log.length - 1`: a read
at `log` answers it). -/
def kvStateOf (l : mvcc.Log) : KVState := ⟨mvcc.stateAfter l, l.length - 1⟩

/-- A write's commit of the changes `cs` at the next revision (none if it changed nothing:
`mvcc.commitLog`'s). -/
def KVState.commit (σ : KVState) (cs : List mvcc.Change) : KVState :=
  if cs = [] then σ else ⟨mvcc.applyChanges (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs cs, σ.rev + 1⟩

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
  unfold kvStateOf KVState.commit mvcc.commitLog
  split
  · rfl
  · simp only [List.length_append, List.length_singleton, KVState.mk.injEq]
    refine ⟨?_, by omega⟩
    rw [mvcc.stateAfter_append]
    congr 2
    omega

/-- **The backend's log follows the state**: the state after a request's backend log is the
request's step on the state before (a log with a revision: the server's always has two). -/
theorem kvStateOf_backendLog (rq : apply.IRRModel) (l : mvcc.Log) (hl : l ≠ []) :
    kvStateOf (backendLog rq l) = kvReqStep rq (kvStateOf l) := by
  have hpos := List.length_pos_iff.2 hl
  have hrev : (kvStateOf l).rev + 1 = l.length := by unfold kvStateOf; simp only; omega
  have hs : (kvStateOf l).kvs = mvcc.stateAfter l := rfl
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
      rw [kvStateOf_commitLog _ _ hl]
      rfl
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

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
  verified proposers send (`putgetKind`; D45, 2026-10-25: no workload parameter, D19q's
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
  /-- (unit T3, 2026-10-24) `LeaseGrant(id, ttl)`, its id fixed before the proposal -/
  | leaseGrant (id ttl : w64)
  /-- (unit T3) `LeaseRevoke(id)` -/
  | leaseRevoke (id : w64)

/-- **A key-value operation** (unit T3): not a lease's grant or revocation. -/
def KVOp.isKV : KVOp → Prop
  | .leaseGrant _ _ => False
  | .leaseRevoke _ => False
  | _ => True

/-- **The KV operation of a request**, by `dispatch`'s kind. -/
def reqKVOp (rq : apply.IRRModel) : Option KVOp :=
  match apply.dispatchKind rq with
  | .put => rq.put.map .put
  | .range => rq.range.map .range
  | .deleteRange => rq.deleteRange.map .deleteRange
  | .txn => rq.txn.map .txn
  | .leaseGrant => rq.leaseGrant.map fun g => .leaseGrant g.id g.ttl
  | .leaseRevoke => rq.leaseRevoke.map .leaseRevoke
  | _ => none

/-- **The kinds the server's verified proposers send**: the KV writes and the monitors' requests
(D45, 2026-10-25: a fact of the proposers, not a parameter; until then D19q's workload record,
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

/-- **A compaction request in M2's scope**, as `EtcdServer.Compact` proposes it
(`&pb.InternalRaftRequest{Compaction: r}`): of the kind `compaction`, at a revision `≥ 1` (M2, the
storage side, 2026-10-30: **M2's scope restriction**, the user's Q7 (a), the approval's item 35: no
compaction at revision `0`, `issues/etcd-restore-scheduled-compact-zero.md`; `EtcdServer.Compact.spec`'s
premise `1 ≤ r`), with no side-effect-free field (`Apply` would skip it without a waiter) and no admin
field (the auth layer's admin check would reject it) beside it (M2's apply side, item 5, review round
1's F-4: so `Apply` dispatches it on every member). `Compact`'s request has nothing else set. -/
def compactPropOk (rq : apply.IRRModel) : Prop :=
  (apply.dispatchKind rq = .compaction ∧ ∃ r : w64, rq.compaction = some r ∧ 1 ≤ sint.Z r) ∧
    apply.noSideEffect rq = false ∧ apply.needAdminPermission rq = false

/-- A plain request is no compaction. -/
theorem plainReq_nonCmp (rq : apply.IRRModel) (h : plainReq rq) :
    apply.dispatchKind rq ≠ .compaction := by
  intro hk
  have := h.2
  rw [hk] at this
  simp [putgetKind] at this

/-- **A plain entry in the cluster's compaction mode `cmp`** (M2's apply side, item 5): a plain
request, or, in compaction mode, a compaction in M2's scope. -/
def plainEntryM (cmp : Bool) (m : EntryModel) : Prop :=
  m.typ = W32 0 → m.data ≠ [] → ∀ rq, apply.irrDecode m.data = some rq →
    plainReq rq ∨ (cmp = true ∧ compactPropOk rq)

/-- **A plain log in the mode `cmp`**: every entry plain in the mode. -/
def plainLogM (cmp : Bool) (A : List EntryModel) : Prop := ∀ m ∈ A, plainEntryM cmp m

theorem plainEntryM_false (m : EntryModel) : plainEntryM false m ↔ plainEntry m := by
  unfold plainEntryM plainEntry
  simp

/-- **Off, a plain log** (the law callers with the mode off need, `kv_log_plain_off`). -/
theorem plainLogM_false (A : List EntryModel) : plainLogM false A ↔ plainLog A := by
  unfold plainLogM plainLog
  simp only [plainEntryM_false]

theorem plainEntryM_of (cmp : Bool) (m : EntryModel) (h : plainEntry m) : plainEntryM cmp m :=
  fun ht hd rq hrq => Or.inl (h ht hd rq hrq)

theorem plainLogM_of (cmp : Bool) (A : List EntryModel) (h : plainLog A) : plainLogM cmp A :=
  fun m hm => plainEntryM_of cmp m (h m hm)

theorem plainLogM_append (cmp : Bool) (A B : List EntryModel) :
    plainLogM cmp (A ++ B) ↔ plainLogM cmp A ∧ plainLogM cmp B := by
  unfold plainLogM
  simp only [List.mem_append]
  exact ⟨fun h => ⟨fun m hm => h m (Or.inl hm), fun m hm => h m (Or.inr hm)⟩,
    fun h m hm => hm.elim (h.1 m) (h.2 m)⟩

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
abbrev srvIdxOkW [GooseExts] (ai₀ : w64) (L : List EntryModel) : Prop :=
  ∀ (n : Nat) (m : EntryModel), L[n]? = some m →
    uint.Z m.index = uint.Z ai₀ + 1 + n ∧
      (m.typ = W32 0 ∨ (m.typ = W32 1 ∧ isConfChangeEncoding m.data))

/-- The log `L` after the applied index `ai₀`: consecutive indices from `ai₀ + 1`, no overflow,
normal entries and v1 conf changes. (The overflow bound is on the *next* index, `ai₀ + 1 + |L|`,
which raft's commit step cannot promise: the KV invariant keeps `srvIdxOkW`, and the bound comes
with a `Ready`'s batch, a premise on the run, `rnLogFits`; 2026-10-16, stage R7b.) -/
def srvIdxOk [GooseExts] (ai₀ : w64) (L : List EntryModel) : Prop :=
  uint.Z ai₀ + 1 + L.length < 2 ^ 64 ∧ srvIdxOkW ai₀ L

/-- A prefix of a consecutive log is consecutive. -/
theorem srvIdxOkW_prefix [GooseExts] (ai₀ : w64) (A B : List EntryModel) (h : srvIdxOkW ai₀ B) (hp : A <+: B) :
    srvIdxOkW ai₀ A := by
  intro n m hm
  obtain ⟨r, rfl⟩ := hp
  exact h n m (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hm).1]; exact hm)

/-- **One entry on** (2026-10-16, stage R7b: what a firing of the server's update gives): the
entry at the next index, normal or a v1 conf change. -/
theorem srvIdxOkW_snoc [GooseExts] (ai₀ : w64) (L : List EntryModel) (e : EntryModel) (h : srvIdxOkW ai₀ L)
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
theorem srvIdxOk_of_W [GooseExts] (ai₀ : w64) (L : List EntryModel) (h : srvIdxOkW ai₀ L)
    (hb : uint.Z ai₀ + 1 + L.length < 2 ^ 64) : srvIdxOk ai₀ L := ⟨hb, h⟩

/-! ## The deterministic step -/

/-- **The lessor's table** (unit T3, 2026-10-24): every live lease's id and granted TTL, in
grant order. Not a function of the mvcc log: a grant makes no revision. -/
abbrev LeaseTable := List (w64 × w64)

/-- The live leases' ids. -/
def LeaseTable.ids (ls : LeaseTable) : List w64 := ls.map Prod.fst

/-- `lessor.Grant`'s maximum TTL (`MaxLeaseTTL`, `lessor.go`). -/
def maxLeaseTTL : Int := 9000000000

/-- **A grant of `id` with TTL `ttl` succeeds at the table `lt`** (unit T3, L3a, 2026-10-26;
`lessor.Grant`): the id is not `NoLease` (`ErrLeaseNotFound`), the TTL at most `MaxLeaseTTL`
(`ErrLeaseTTLTooLarge`), the id not live (`ErrLeaseExists`). -/
def leaseGrantOk (lt : LeaseTable) (id ttl : w64) : Prop :=
  id ≠ W64 0 ∧ sint.Z ttl ≤ maxLeaseTTL ∧ id ∉ lt.ids

instance (lt : LeaseTable) (id ttl : w64) : Decidable (leaseGrantOk lt id ttl) := by
  unfold leaseGrantOk; infer_instance

/-- A put's lease is set and not in the table (`ErrLeaseNotFound`, the request rejected). -/
def leaseMissingIn (lt : LeaseTable) (l : w64) : Prop := l ≠ W64 0 ∧ l ∉ lt.ids

instance (lt : LeaseTable) (l : w64) : Decidable (leaseMissingIn lt l) := by
  unfold leaseMissingIn; infer_instance

/-- **A revocation's deletions** (unit T3): every key attached to `id`, in key order (the
lessor's `Revoke` sorts its item set; the state is sorted by key). -/
def revokeChanges (s : List EtcdKv) (id : w64) : List mvcc.Change :=
  (s.filter (fun v => v.lease = id)).map fun v => .del v.key

open Classical in
/-- **The backend's effect on the log**, deterministically (`apply.backendStep`'s outcome for a
plain request), at the lease table `lt` (unit T3, L3a): a put naming a lease not in the table, or
not finding the previous key-value an ignore flag needs, is rejected, else its change appended; a
delete commits its range's deletions; a transaction whose path does not find a previous key-value
it needs or names a lease not in the table is rejected (`checkTxn`), else the server's run
committed; a revocation of a live lease deletes its keys at one revision. -/
def backendLog (lt : LeaseTable) (rq : apply.IRRModel) (log : mvcc.Log) : mvcc.Log :=
  match apply.dispatchKind rq with
  | .put =>
      match rq.put with
      | some op =>
        if leaseMissingIn lt op.leaseID then log
        else if txn.needsPrev op && (mvcc.findKey op.key (mvcc.stateAfter log)).isNone then log
        else log ++ [[txn.putChangeOf op (mvcc.findKey op.key (mvcc.stateAfter log))]]
      | none => log
  | .deleteRange =>
      match rq.deleteRange with
      | some op => mvcc.commitLog log (txn.delChanges (mvcc.stateAfter log) op)
      | none => log
  | .txn =>
      match rq.txn with
      | some t =>
        if txn.PathsIgnOk (mvcc.stateAfter log) (t.branch (txn.txnOk (mvcc.stateAfter log) t)) ∧
            txn.PathsLeaseOk (mvcc.stateAfter log) lt.ids
              (t.branch (txn.txnOk (mvcc.stateAfter log) t)) then
          mvcc.commitLog log (txn.srvRunTxn (W64 (log.length : Int)) (mvcc.stateAfter log) t).2.1
        else log
      | none => log
  | .leaseRevoke =>
      match rq.leaseRevoke with
      | some id =>
        if id ∈ lt.ids then mvcc.commitLog log (revokeChanges (mvcc.stateAfter log) id) else log
      | none => log
  | _ => log

open Classical in
/-- **The backend's effect on the lease table** (unit T3, L3a): a grant that succeeds
(`leaseGrantOk`) appends its lease, a revocation of a live lease removes it; nothing else changes
it (it does not depend on the log). -/
def backendTable (rq : apply.IRRModel) (lt : LeaseTable) : LeaseTable :=
  match apply.dispatchKind rq with
  | .leaseGrant =>
      match rq.leaseGrant with
      | some g => if leaseGrantOk lt g.id g.ttl then lt ++ [(g.id, g.ttl)] else lt
      | none => lt
  | .leaseRevoke =>
      match rq.leaseRevoke with
      | some id => if id ∈ lt.ids then lt.filter (fun p => p.1 ≠ id) else lt
      | none => lt
  | _ => lt

/-- A request the generic proofs cover changes no table (unit T3, L3a: `plainCover` admits no
lease kind). -/
theorem backendTable_plain (rq : apply.IRRModel) (lt : LeaseTable) (hp : plainCover rq) :
    backendTable rq lt = lt := by
  unfold backendTable
  split
  · rename_i hk; unfold plainCover at hp; rw [hk] at hp; exact hp.elim
  · rename_i hk; unfold plainCover at hp; rw [hk] at hp; exact hp.elim
  · rfl

/-- **The chain's effect on the log**, deterministically: the corrupt and capped layers reject
what they always reject; the auth layer lets everything through (auth disabled); the quota layer
changes no log. -/
def chainLog : apply.Chain → apply.IRRModel → LeaseTable → mvcc.Log → mvcc.Log
  | .backend, rq, lt, log => backendLog lt rq log
  | .corrupt c, rq, lt, log =>
      if apply.corruptRejects (apply.dispatchKind rq) then log else chainLog c rq lt log
  | .capped c, rq, lt, log =>
      if apply.cappedRejects (apply.dispatchKind rq) then log else chainLog c rq lt log
  | .auth _ c, rq, lt, log => chainLog c rq lt log
  | .quota c, rq, lt, log => chainLog c rq lt log

/-- **The chain's effect on the lease table** (unit T3, L3a), as `chainLog`'s on the log. -/
def chainTable : apply.Chain → apply.IRRModel → LeaseTable → LeaseTable
  | .backend, rq, lt => backendTable rq lt
  | .corrupt c, rq, lt =>
      if apply.corruptRejects (apply.dispatchKind rq) then lt else chainTable c rq lt
  | .capped c, rq, lt =>
      if apply.cappedRejects (apply.dispatchKind rq) then lt else chainTable c rq lt
  | .auth _ c, rq, lt => chainTable c rq lt
  | .quota c, rq, lt => chainTable c rq lt

/-- **`dispatch(rq, v3)`'s effect on the log**, deterministically (`apply.dispatchStep`). -/
def dispatchLog (c : apply.Chain) (rq : apply.IRRModel) (v3 : Bool) (lt : LeaseTable)
    (log : mvcc.Log) : mvcc.Log :=
  if apply.preV3Kind (apply.dispatchKind rq) = true ∨ v3 = false then log
  else if apply.storeKind (apply.dispatchKind rq) = true then chainLog c rq lt log
  else log

/-- **`dispatch(rq, v3)`'s effect on the lease table** (unit T3, L3a): a grant is dispatched to the
chain too (`applyV3.LeaseGrant`), though not a store kind (it changes no log). -/
def dispatchTable (c : apply.Chain) (rq : apply.IRRModel) (v3 : Bool) (lt : LeaseTable) :
    LeaseTable :=
  if apply.preV3Kind (apply.dispatchKind rq) = true ∨ v3 = false then lt
  else chainTable c rq lt

/-- **An entry's effect on the log**, from the consistent index `c₀` with the chain `ch`: a normal
entry with data that decodes is dispatched (`v3` iff above `c₀`); nothing else changes the log.
(Unit T3, L3a) At the lease table `lt`. -/
def kvEntry (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (log : mvcc.Log) (m : EntryModel) :
    mvcc.Log :=
  if m.typ = W32 0 then
    if m.data = [] then log
    else match apply.irrDecode m.data with
      | some rq => dispatchLog ch rq (decide (uint.Z c₀ < uint.Z m.index)) lt log
      | none => log
  else log

/-- **An entry's effect on the lease table** (unit T3, L3a), as `kvEntry`'s on the log. -/
def kvTable (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (m : EntryModel) : LeaseTable :=
  if m.typ = W32 0 then
    if m.data = [] then lt
    else match apply.irrDecode m.data with
      | some rq => dispatchTable ch rq (decide (uint.Z c₀ < uint.Z m.index)) lt
      | none => lt
  else lt

/-- **An entry's effect on the log and the lease table** (unit T3, L3a). -/
def kvEntrySt (c₀ : w64) (ch : apply.Chain) (s : mvcc.Log × LeaseTable) (m : EntryModel) :
    mvcc.Log × LeaseTable :=
  (kvEntry c₀ ch s.2 s.1 m, kvTable c₀ ch s.2 m)

/-- **The lease table of a raft log** `A` from the table `lt₀` (unit T3, L3a). -/
def kvTableOf (c₀ : w64) (ch : apply.Chain) (lt₀ : LeaseTable) (A : List EntryModel) : LeaseTable :=
  A.foldl (kvTable c₀ ch) lt₀

/-- **The model of a raft log** `A`, the log and the lease table, from `s₀` (unit T3, L3a). -/
def kvRaftSt (c₀ : w64) (ch : apply.Chain) (s₀ : mvcc.Log × LeaseTable) (A : List EntryModel) :
    mvcc.Log × LeaseTable :=
  A.foldl (kvEntrySt c₀ ch) s₀

/-- **The KV model of a raft log** `A` (the entries after the start index), from the log `log₀`
at the start (the snapshot's), the consistent index `c₀` and the chain `ch`; (unit T3, L3a) each
entry at the lease table of the entries before it, from the empty table (the lessor `NewLessor`
gives has no lease). -/
def kvRaftOf (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) (A : List EntryModel) : mvcc.Log :=
  (kvRaftSt c₀ ch (log₀, []) A).1

/-- **The value of `k`** in the state after `log`. -/
def kvVal (log : mvcc.Log) (k : GoString) : Option GoString :=
  (mvcc.findKey k (mvcc.stateAfter log)).map EtcdKv.value

theorem kvRaftSt_nil (c₀ : w64) (ch : apply.Chain) (s₀ : mvcc.Log × LeaseTable) :
    kvRaftSt c₀ ch s₀ [] = s₀ := rfl

theorem kvRaftSt_append (c₀ : w64) (ch : apply.Chain) (s₀ : mvcc.Log × LeaseTable)
    (A B : List EntryModel) :
    kvRaftSt c₀ ch s₀ (A ++ B) = kvRaftSt c₀ ch (kvRaftSt c₀ ch s₀ A) B := by
  unfold kvRaftSt; exact List.foldl_append

theorem kvRaftSt_snoc (c₀ : w64) (ch : apply.Chain) (s₀ : mvcc.Log × LeaseTable)
    (A : List EntryModel) (m : EntryModel) :
    kvRaftSt c₀ ch s₀ (A ++ [m]) = kvEntrySt c₀ ch (kvRaftSt c₀ ch s₀ A) m := by
  rw [kvRaftSt_append]; rfl

/-- The model's table is the entries' table (it does not depend on the log). -/
theorem kvRaftSt_snd (c₀ : w64) (ch : apply.Chain) (A : List EntryModel) :
    ∀ s₀ : mvcc.Log × LeaseTable, (kvRaftSt c₀ ch s₀ A).2 = kvTableOf c₀ ch s₀.2 A := by
  induction A with
  | nil => intro s₀; rfl
  | cons m A ih => intro s₀; exact ih (kvEntrySt c₀ ch s₀ m)

theorem kvTableOf_snoc (c₀ : w64) (ch : apply.Chain) (lt₀ : LeaseTable) (A : List EntryModel)
    (m : EntryModel) : kvTableOf c₀ ch lt₀ (A ++ [m]) = kvTable c₀ ch (kvTableOf c₀ ch lt₀ A) m := by
  unfold kvTableOf; rw [List.foldl_append]; rfl

theorem kvRaftOf_nil (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) : kvRaftOf c₀ ch log₀ [] = log₀ := rfl

/-- **An entry's step on the model** (unit T3, L3a: at the table of the entries before it). -/
theorem kvRaftOf_snoc (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) (A : List EntryModel)
    (m : EntryModel) :
    kvRaftOf c₀ ch log₀ (A ++ [m]) = kvEntry c₀ ch (kvTableOf c₀ ch [] A) (kvRaftOf c₀ ch log₀ A) m := by
  unfold kvRaftOf
  rw [kvRaftSt_snoc, ← kvRaftSt_snd c₀ ch A (log₀, [])]
  rfl

/-! ## Shape: at most one revision per entry -/

theorem commitLog_grow (log : mvcc.Log) (pend : List mvcc.Change) :
    mvcc.commitLog log pend = log ∨ ∃ cs, mvcc.commitLog log pend = log ++ [cs] := by
  unfold mvcc.commitLog
  split
  · left; rfl
  · right; exact ⟨_, rfl⟩

theorem backendLog_grow (lt : LeaseTable) (rq : apply.IRRModel) (log : mvcc.Log) :
    backendLog lt rq log = log ∨ ∃ cs, backendLog lt rq log = log ++ [cs] := by
  unfold backendLog
  split
  · split
    · split
      · left; rfl
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
  · split
    · split
      · exact commitLog_grow _ _
      · left; rfl
    · left; rfl
  · left; rfl

theorem chainLog_grow : ∀ (c : apply.Chain) (rq : apply.IRRModel) (lt : LeaseTable) (log : mvcc.Log),
    chainLog c rq lt log = log ∨ ∃ cs, chainLog c rq lt log = log ++ [cs]
  | .backend, rq, lt, log => backendLog_grow lt rq log
  | .corrupt c, rq, lt, log => by
    simp only [chainLog]; split
    · left; rfl
    · exact chainLog_grow c rq lt log
  | .capped c, rq, lt, log => by
    simp only [chainLog]; split
    · left; rfl
    · exact chainLog_grow c rq lt log
  | .auth _ c, rq, lt, log => by simp only [chainLog]; exact chainLog_grow c rq lt log
  | .quota c, rq, lt, log => by simp only [chainLog]; exact chainLog_grow c rq lt log

theorem dispatchLog_grow (c : apply.Chain) (rq : apply.IRRModel) (v3 : Bool) (lt : LeaseTable)
    (log : mvcc.Log) :
    dispatchLog c rq v3 lt log = log ∨ ∃ cs, dispatchLog c rq v3 lt log = log ++ [cs] := by
  unfold dispatchLog
  split
  · left; rfl
  · split
    · exact chainLog_grow c rq lt log
    · left; rfl

/-- **An entry appends at most one revision.** -/
theorem kvEntry_grow (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (log : mvcc.Log)
    (m : EntryModel) :
    kvEntry c₀ ch lt log m = log ∨ ∃ cs, kvEntry c₀ ch lt log m = log ++ [cs] := by
  unfold kvEntry
  split
  · split
    · left; rfl
    · split
      · exact dispatchLog_grow _ _ _ _ _
      · left; rfl
  · left; rfl

theorem kvEntry_prefix (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (log : mvcc.Log)
    (m : EntryModel) : log <+: kvEntry c₀ ch lt log m := by
  rcases kvEntry_grow c₀ ch lt log m with h | ⟨cs, h⟩
  · rw [h]; exact List.prefix_refl _
  · rw [h]; exact List.prefix_append _ _

theorem kvRaftSt_extends (c₀ : w64) (ch : apply.Chain) (A : List EntryModel) :
    ∀ s₀ : mvcc.Log × LeaseTable, s₀.1 <+: (kvRaftSt c₀ ch s₀ A).1 := by
  induction A with
  | nil => intro s₀; exact List.prefix_refl _
  | cons m A ih =>
    intro s₀
    exact (kvEntry_prefix c₀ ch s₀.2 s₀.1 m).trans (ih (kvEntrySt c₀ ch s₀ m))

theorem kvRaftOf_extends (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) (A : List EntryModel) :
    log₀ <+: kvRaftOf c₀ ch log₀ A :=
  kvRaftSt_extends c₀ ch A (log₀, [])

/-- **The model grows with the raft log.** -/
theorem kvRaftOf_prefix (c₀ : w64) (ch : apply.Chain) (log₀ : mvcc.Log) (A B : List EntryModel)
    (h : A <+: B) : kvRaftOf c₀ ch log₀ A <+: kvRaftOf c₀ ch log₀ B := by
  obtain ⟨D, rfl⟩ := h
  unfold kvRaftOf
  rw [kvRaftSt_append]
  exact kvRaftSt_extends _ _ _ _


/-! ## A plain put's and a write-free request's effect on the values -/

section putValues
open mvcc

end putValues

/-- **A write kind**: a put, a delete or a transaction (2026-10-15, unit T2: a transaction too);
(unit T3, L3a) a lease's grant or revocation (the table, and a revocation's deletions). -/
def writeKind (k : apply.ReqKind) : Prop :=
  k = .put ∨ k = .deleteRange ∨ k = .txn ∨ k = .leaseGrant ∨ k = .leaseRevoke

/-- A request that is no write changes no log through any chain. -/
theorem chainLog_nonwrite (rq : apply.IRRModel) (lt : LeaseTable) (log : mvcc.Log)
    (hk : ¬ writeKind (apply.dispatchKind rq)) :
    ∀ c : apply.Chain, chainLog c rq lt log = log := by
  intro c
  unfold writeKind at hk
  induction c with
  | backend =>
    simp only [chainLog, backendLog]
    split
    · rename_i hk'; exact absurd (Or.inl hk') hk
    · rename_i hk'; exact absurd (Or.inr (Or.inl hk')) hk
    · rename_i hk'; exact absurd (Or.inr (Or.inr (Or.inl hk'))) hk
    · rename_i hk'; exact absurd (Or.inr (Or.inr (Or.inr (Or.inr hk')))) hk
    · rfl
  | corrupt c ih => simp only [chainLog]; split <;> simp [ih]
  | capped c ih => simp only [chainLog]; split <;> simp [ih]
  | auth _ c ih => simp only [chainLog]; exact ih
  | quota c ih => simp only [chainLog]; exact ih

/-- A request that is no write changes no table through any chain. -/
theorem chainTable_nonwrite (rq : apply.IRRModel) (lt : LeaseTable)
    (hk : ¬ writeKind (apply.dispatchKind rq)) :
    ∀ c : apply.Chain, chainTable c rq lt = lt := by
  intro c
  unfold writeKind at hk
  induction c with
  | backend =>
    simp only [chainTable, backendTable]
    split
    · rename_i hk'; exact absurd (Or.inr (Or.inr (Or.inr (Or.inl hk')))) hk
    · rename_i hk'; exact absurd (Or.inr (Or.inr (Or.inr (Or.inr hk')))) hk
    · rfl
  | corrupt c ih => simp only [chainTable]; split <;> simp [ih]
  | capped c ih => simp only [chainTable]; split <;> simp [ih]
  | auth _ c ih => simp only [chainTable]; exact ih
  | quota c ih => simp only [chainTable]; exact ih

/-- **A write-free entry keeps the model** (an empty entry, a conf change, or a request that is
no write). -/
theorem kvEntry_nonwrite (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (log : mvcc.Log)
    (e : EntryModel)
    (h : e.data = [] ∨ e.typ ≠ W32 0 ∨ ∀ rq, apply.irrDecode e.data = some rq →
      ¬ writeKind (apply.dispatchKind rq)) :
    kvEntry c₀ ch lt log e = log := by
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
            · exact chainLog_nonwrite rq lt log (h rq hdec) ch
            · rfl
      · rfl
  · rfl

/-- **A write-free entry keeps the table** (unit T3, L3a). -/
theorem kvTable_nonwrite (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (e : EntryModel)
    (h : e.data = [] ∨ e.typ ≠ W32 0 ∨ ∀ rq, apply.irrDecode e.data = some rq →
      ¬ writeKind (apply.dispatchKind rq)) :
    kvTable c₀ ch lt e = lt := by
  unfold kvTable
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
        · unfold dispatchTable
          split
          · rfl
          · exact chainTable_nonwrite rq lt (h rq hdec) ch
      · rfl
  · rfl

/-- **`dispatch` through the base chain, with `v3`, is the backend's** (whatever the kind: the
pre-v3 kinds and the kinds the chain does not run change no log, as the backend's model). -/
theorem dispatchLog_base (rq : apply.IRRModel) (lt : LeaseTable) (log : mvcc.Log) :
    dispatchLog (apply.alarmChain false false false) rq true lt log = backendLog lt rq log := by
  have hb : chainLog (apply.alarmChain false false false) rq lt log = backendLog lt rq log := by
    simp only [apply.alarmChain, apply.baseChain, Bool.false_eq_true, ↓reduceIte, chainLog]
  have hnw : ¬ writeKind (apply.dispatchKind rq) → backendLog lt rq log = log := by
    intro hk
    have := chainLog_nonwrite rq lt log hk .backend
    simpa only [chainLog] using this
  unfold dispatchLog
  rw [hb]
  split
  · rename_i h
    rcases h with h | h
    · rw [hnw]
      unfold writeKind
      intro hk; rcases hk with hk | hk | hk | hk | hk <;> rw [hk] at h <;> cases h
    · cases h
  · split
    · rfl
    · rename_i _ h
      unfold backendLog
      split <;> first | rfl | (rename_i hk; rw [hk] at h; exact absurd rfl h)

/-- **`dispatch`'s table through the base chain, with `v3`, is the backend's** (unit T3, L3a). -/
theorem dispatchTable_base (rq : apply.IRRModel) (lt : LeaseTable) :
    dispatchTable (apply.alarmChain false false false) rq true lt = backendTable rq lt := by
  have hb : chainTable (apply.alarmChain false false false) rq lt = backendTable rq lt := by
    simp only [apply.alarmChain, apply.baseChain, Bool.false_eq_true, ↓reduceIte, chainTable]
  unfold dispatchTable
  rw [hb]
  split
  · rename_i h
    rcases h with h | h
    · unfold backendTable
      split <;> first | rfl | (rename_i hk; rw [hk] at h; cases h)
    · cases h
  · rfl

/-- **An entry above the consistent index, through the base chain**: its request's backend log
(2026-10-15, unit T2; it was `kvEntry_put`, for a put). -/
theorem kvEntry_base (c₀ : w64) (lt : LeaseTable) (log : mvcc.Log) (e : EntryModel)
    (rq : apply.IRRModel) (ht : e.typ = W32 0) (hd : e.data ≠ [])
    (hdec : apply.irrDecode e.data = some rq) (hidx : uint.Z c₀ < uint.Z e.index) :
    kvEntry c₀ (apply.alarmChain false false false) lt log e = backendLog lt rq log := by
  unfold kvEntry
  rw [if_pos ht, if_neg hd, hdec]
  simp only
  rw [decide_eq_true hidx]
  exact dispatchLog_base rq lt log

/-- A covered request changes no table through any chain (unit T3, L3a). -/
theorem chainTable_plain (rq : apply.IRRModel) (lt : LeaseTable) (hp : plainCover rq) :
    ∀ c : apply.Chain, chainTable c rq lt = lt := by
  intro c
  induction c with
  | backend => exact backendTable_plain rq lt hp
  | corrupt c ih => simp only [chainTable]; split <;> simp [ih]
  | capped c ih => simp only [chainTable]; split <;> simp [ih]
  | auth _ c ih => simp only [chainTable]; exact ih
  | quota c ih => simp only [chainTable]; exact ih

/-- A plain entry changes no table (unit T3, L3a: until lease requests are admitted, the committed
log's table stays empty). -/
theorem kvTable_plain (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (m : EntryModel)
    (hp : plainEntry m) : kvTable c₀ ch lt m = lt := by
  unfold kvTable
  split
  · rename_i ht
    split
    · rfl
    · rename_i hd
      split
      · rename_i rq hdec
        unfold dispatchTable
        split
        · rfl
        · exact chainTable_plain rq lt (hp ht hd rq hdec).1 ch
      · rfl
  · rfl

/-- A compaction is no write (M2's apply side). -/
theorem compactPropOk_nonwrite (rq : apply.IRRModel) (h : compactPropOk rq) :
    ¬ writeKind (apply.dispatchKind rq) := by
  rw [h.1.1]
  unfold writeKind
  simp

/-- **An entry plain in the mode changes no table** (a compaction is no write). -/
theorem kvTable_plainM (c₀ : w64) (ch : apply.Chain) (lt : LeaseTable) (cmp : Bool)
    (m : EntryModel) (hp : plainEntryM cmp m) : kvTable c₀ ch lt m = lt := by
  unfold kvTable
  split
  · rename_i ht
    split
    · rfl
    · rename_i hd
      split
      · rename_i rq hdec
        unfold dispatchTable
        split
        · rfl
        · rcases hp ht hd rq hdec with h | ⟨-, h⟩
          · exact chainTable_plain rq lt h.1 ch
          · exact chainTable_nonwrite rq lt (compactPropOk_nonwrite rq h) ch
      · rfl
  · rfl

/-- A log plain in the mode changes no table. -/
theorem kvTableOf_plainM (c₀ : w64) (ch : apply.Chain) (cmp : Bool) (A : List EntryModel)
    (hp : plainLogM cmp A) : ∀ lt, kvTableOf c₀ ch lt A = lt := by
  induction A with
  | nil => intro lt; rfl
  | cons m A ih =>
    intro lt
    show kvTableOf c₀ ch (kvTable c₀ ch lt m) A = lt
    rw [kvTable_plainM c₀ ch lt cmp m (hp m (List.mem_cons_self ..))]
    exact ih (fun m' hm' => hp m' (List.mem_cons_of_mem _ hm')) lt

/-- A plain log changes no table. -/
theorem kvTableOf_plain (c₀ : w64) (ch : apply.Chain) (A : List EntryModel) (hp : plainLog A) :
    ∀ lt, kvTableOf c₀ ch lt A = lt :=
  kvTableOf_plainM c₀ ch false A ((plainLogM_false A).2 hp)

/-- **An entry's table above the consistent index, through the base chain**: its request's
backend table (unit T3, L3a). -/
theorem kvTable_base (c₀ : w64) (lt : LeaseTable) (e : EntryModel) (rq : apply.IRRModel)
    (ht : e.typ = W32 0) (hd : e.data ≠ []) (hdec : apply.irrDecode e.data = some rq)
    (hidx : uint.Z c₀ < uint.Z e.index) :
    kvTable c₀ (apply.alarmChain false false false) lt e = backendTable rq lt := by
  unfold kvTable
  rw [if_pos ht, if_neg hd, hdec]
  simp only
  rw [decide_eq_true hidx]
  exact dispatchTable_base rq lt

/-! ## etcd's KV state, at every revision it keeps (D47, 2026-10-25; D46 kept a store per revision)

The abstract state of etcd's KV as its clients see it (`KVState`), as etcd's mvcc keeps it: the
store at the compaction revision (`base`, a finite map from keys to their records, `KVStore`,
`KVStore.lean`) and, for each later revision, its changes in order (`changes`; mvcc's key bucket
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
  changes : List (List mvcc.Change)
  /-- (unit T3) the lessor's table -/
  leases : LeaseTable := []

/-- **The key-values after the revisions `l`**, applied in order from `s`, the first of them
revision `r0 + 1` (`mvcc.stateAfter`'s step: each revision's changes at its own revision). -/
def runFrom (r0 : Nat) (s : List EtcdKv) : List (List mvcc.Change) → List EtcdKv
  | [] => s
  | cs :: l => runFrom (r0 + 1) (mvcc.applyChanges (W64 ((r0 + 1 : Nat) : Int)) s cs) l

/-- **The current revision.** -/
def KVState.rev (σ : KVState) : Nat := σ.compacted + σ.changes.length

/-- **The store at revision `r`** (one of `compacted`, ..., `rev`; empty below `compacted`, the
current store above `rev`): the base with the changes of the revisions up to `r`. -/
def KVState.at (σ : KVState) (r : Nat) : KVStore :=
  if r < σ.compacted then ∅
  else storeOf (runFrom σ.compacted σ.base.kvs (σ.changes.take (r - σ.compacted)))

/-- **The changes of revision `r`** (one of `compacted + 1`, ..., `rev`; none outside), in order. -/
def KVState.changesAt (σ : KVState) (r : Nat) : List mvcc.Change :=
  if r ≤ σ.compacted then [] else (σ.changes[r - σ.compacted - 1]?).getD []

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
    (σ.at r).kvs = runFrom σ.compacted σ.base.kvs (σ.changes.take (r - σ.compacted)) := by
  unfold KVState.at
  rw [if_neg (by omega), kvs_storeOf _ (runFrom_sorted _ _ (KVStore.kvs_sorted _))]

theorem KVState.kvs_eq (σ : KVState) : σ.kvs = runFrom σ.compacted σ.base.kvs σ.changes := by
  unfold KVState.kvs KVState.store
  rw [KVState.at_kvs σ σ.rev (by unfold KVState.rev; omega),
    List.take_of_length_le (by unfold KVState.rev; omega)]

/-- **The state of a log**: its first revision's store, then each later revision's changes, none
compacted; its current revision the log's last (`log.length - 1`: a read at `log` answers it);
(unit T3, L3a) the lease table `lt` (none by default). -/
def kvStateOf (l : mvcc.Log) (lt : LeaseTable := []) : KVState :=
  { compacted := 0, base := storeOf (mvcc.stateAt l 0), changes := l.drop 1, leases := lt }

/-- A write's commit of the changes `cs` at the next revision (none if it changed nothing:
`mvcc.commitLog`'s); the lease table unchanged. -/
def KVState.commit (σ : KVState) (cs : List mvcc.Change) : KVState :=
  if cs = [] then σ else { σ with changes := σ.changes ++ [cs] }

theorem KVState.kvs_sorted (σ : KVState) : σ.kvs.Pairwise etcdKvLess := KVStore.kvs_sorted _

theorem kvStateOf_rev (l : mvcc.Log) {lt : LeaseTable} : (kvStateOf l lt).rev = l.length - 1 := by
  simp [kvStateOf, KVState.rev]

theorem kvStateOf_compacted (l : mvcc.Log) {lt : LeaseTable} : (kvStateOf l lt).compacted = 0 := rfl

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
theorem kvStateOf_at (l : mvcc.Log) {lt : LeaseTable} (r : Nat) (hr : r ≤ l.length - 1) :
    (kvStateOf l lt).at r = storeOf (mvcc.stateAt l r) := by
  unfold kvStateOf KVState.at
  simp only [Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]
  rw [kvs_storeOf _ (mvcc.stateAt_sorted l 0)]
  have := runFrom_stateAt l r 0 (by omega)
  simp only [Nat.zero_add] at this
  rw [this]

/-- Revision `r`'s key-values of a log's state are the log's state at `r`. -/
theorem kvStateOf_at_kvs (l : mvcc.Log) {lt : LeaseTable} (r : Nat) (hr : r ≤ l.length - 1) :
    ((kvStateOf l lt).at r).kvs = mvcc.stateAt l r := by
  rw [kvStateOf_at l r hr, kvs_storeOf _ (mvcc.stateAt_sorted l r)]

theorem kvStateOf_store (l : mvcc.Log) {lt : LeaseTable} : (kvStateOf l lt).store = storeOf (mvcc.stateAfter l) := by
  unfold KVState.store
  rw [kvStateOf_rev, kvStateOf_at l _ (Nat.le_refl _), mvcc.stateAt_last]

theorem kvStateOf_kvs (l : mvcc.Log) {lt : LeaseTable} : (kvStateOf l lt).kvs = mvcc.stateAfter l := by
  unfold KVState.kvs
  rw [kvStateOf_store, kvs_storeOf _ (mvcc.stateAfter_sorted l)]

/-- Revision `r`'s changes in a log's state are the log's (`r` a later revision). -/
theorem kvStateOf_changesAt (l : mvcc.Log) {lt : LeaseTable} (r : Nat) (h0 : 0 < r) :
    (kvStateOf l lt).changesAt r = l.getD r [] := by
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
    · have : r - σ.compacted ≤ σ.changes.length := by unfold KVState.rev at hr; omega
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
    · have : r - σ.compacted - 1 < σ.changes.length := by unfold KVState.rev at hr; omega
      rw [List.getElem?_append_left this]

/-- A put's lease is set and not live (unit T3: `ErrLeaseNotFound`, the request rejected). -/
def KVState.leaseMissing (σ : KVState) (l : w64) : Prop := l ≠ W64 0 ∧ l ∉ σ.leases.ids

instance (σ : KVState) (l : w64) : Decidable (σ.leaseMissing l) := by
  unfold KVState.leaseMissing; infer_instance

theorem KVState.leaseMissing_zero (σ : KVState) : ¬ σ.leaseMissing (W64 0) := by
  simp [KVState.leaseMissing]

open Classical in
/-- **The operation's effect on the state**: a put not finding the previous key-value its
ignore flag needs changes nothing, else commits its one change; a range changes nothing; a
delete commits its range's deletions; a transaction whose path does not find a previous
key-value it needs changes nothing (`checkTxn`'s error), else commits the server's run
(`srvRunTxn`, nested branches by their verdicts at the state). (Unit T3) A put or transaction
naming a lease not in the table changes nothing (`ErrLeaseNotFound`); a grant that succeeds
(`leaseGrantOk`) adds its lease to the table; a revocation of a live lease deletes its keys at one
revision and removes it. -/
def kvOpStep : KVOp → KVState → KVState
  | .put o, σ =>
    if σ.leaseMissing o.leaseID then σ
    else if txn.needsPrev o && (mvcc.findKey o.key σ.kvs).isNone then σ
    else σ.commit [txn.putChangeOf o (mvcc.findKey o.key σ.kvs)]
  | .range _, σ => σ
  | .deleteRange o, σ => σ.commit (txn.delChanges σ.kvs o)
  | .txn t, σ =>
    if txn.PathsIgnOk σ.kvs (t.branch (txn.txnOk σ.kvs t)) ∧
        txn.PathsLeaseOk σ.kvs σ.leases.ids (t.branch (txn.txnOk σ.kvs t)) then
      σ.commit (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs t).2.1
    else σ
  | .leaseGrant id ttl, σ =>
    if leaseGrantOk σ.leases id ttl then { σ with leases := σ.leases ++ [(id, ttl)] } else σ
  | .leaseRevoke id, σ =>
    if id ∈ σ.leases.ids then
      { σ.commit (revokeChanges σ.kvs id) with leases := σ.leases.filter (fun p => p.1 ≠ id) }
    else σ

/-- **A request's effect on the state**: its operation's, or none. -/
def kvReqStep (rq : apply.IRRModel) (σ : KVState) : KVState :=
  match reqKVOp rq with
  | some op => kvOpStep op σ
  | none => σ

theorem kvStateOf_commitLog (l : mvcc.Log) {lt : LeaseTable} (cs : List mvcc.Change) (hl : l ≠ []) :
    kvStateOf (mvcc.commitLog l cs) lt = (kvStateOf l lt).commit cs := by
  have hpos := List.length_pos_iff.2 hl
  unfold mvcc.commitLog
  by_cases hc : cs = []
  · simp [hc, KVState.commit_nil]
  rw [if_neg hc]
  unfold KVState.commit kvStateOf
  rw [if_neg hc, mvcc.stateAt_append_lt _ _ hpos, List.drop_append_of_le_length (by omega)]

/-- A commit keeps the table. -/
theorem KVState.commit_leases (σ : KVState) (cs : List mvcc.Change) :
    (σ.commit cs).leases = σ.leases := by
  unfold KVState.commit; split <;> rfl

/-- **The backend's log follows the state**: the state after a request's backend log, at the
backend's table after it, is the request's step on the state before (a log with a revision: the
server's always has two); (unit T3, L3a) at any table, for any request. -/
theorem kvStateOf_backendLog (lt : LeaseTable) (rq : apply.IRRModel) (l : mvcc.Log) (hl : l ≠ []) :
    kvStateOf (backendLog lt rq l) (backendTable rq lt) = kvReqStep rq (kvStateOf l lt) := by
  have hpos := List.length_pos_iff.2 hl
  have hrev : (kvStateOf l lt).rev + 1 = l.length := by rw [kvStateOf_rev]; omega
  have hs : (kvStateOf l lt).kvs = mvcc.stateAfter l := kvStateOf_kvs l
  have hT : apply.dispatchKind rq ≠ .leaseGrant → apply.dispatchKind rq ≠ .leaseRevoke →
      backendTable rq lt = lt := by
    intro h1 h2; unfold backendTable; split <;> first | rfl | contradiction
  unfold backendLog kvReqStep reqKVOp
  cases hk : apply.dispatchKind rq
  case put =>
    rw [hT (by rw [hk]; decide) (by rw [hk]; decide)]
    dsimp only
    cases hp : rq.put with
    | none => rfl
    | some op =>
      simp only [Option.map_some, kvOpStep]
      by_cases hm : leaseMissingIn lt op.leaseID
      · rw [if_pos hm, if_pos (show (kvStateOf l lt).leaseMissing op.leaseID from hm)]
      rw [if_neg hm, if_neg (show ¬ (kvStateOf l lt).leaseMissing op.leaseID from hm), hs]
      split
      · rfl
      · have : l ++ [[txn.putChangeOf op (mvcc.findKey op.key (mvcc.stateAfter l))]] =
            mvcc.commitLog l [txn.putChangeOf op (mvcc.findKey op.key (mvcc.stateAfter l))] := by
          simp [mvcc.commitLog]
        rw [this, kvStateOf_commitLog _ _ hl]
  case range =>
    rw [hT (by rw [hk]; decide) (by rw [hk]; decide)]
    dsimp only
    cases hp : rq.range with
    | none => rfl
    | some o => rfl
  case deleteRange =>
    rw [hT (by rw [hk]; decide) (by rw [hk]; decide)]
    dsimp only
    cases hp : rq.deleteRange with
    | none => rfl
    | some op =>
      simp only [Option.map_some, kvOpStep]
      rw [kvStateOf_commitLog _ _ hl, hs]
  case txn =>
    rw [hT (by rw [hk]; decide) (by rw [hk]; decide)]
    dsimp only
    cases hp : rq.txn with
    | none => rfl
    | some t =>
      simp only [Option.map_some, kvOpStep]
      rw [hs, hrev, show (kvStateOf l lt).leases = lt from rfl]
      by_cases hi : txn.PathsIgnOk (mvcc.stateAfter l) (t.branch (txn.txnOk (mvcc.stateAfter l) t)) ∧
          txn.PathsLeaseOk (mvcc.stateAfter l) lt.ids (t.branch (txn.txnOk (mvcc.stateAfter l) t))
      · rw [if_pos hi, if_pos hi, kvStateOf_commitLog _ _ hl]
      · rw [if_neg hi, if_neg hi]
  case leaseGrant =>
    dsimp only
    unfold backendTable
    rw [hk]
    dsimp only
    cases hp : rq.leaseGrant with
    | none => rfl
    | some g =>
      simp only [Option.map_some, kvOpStep]
      by_cases hg : leaseGrantOk lt g.id g.ttl
      · rw [if_pos hg, if_pos (show leaseGrantOk (kvStateOf l lt).leases g.id g.ttl from hg)]; rfl
      · rw [if_neg hg, if_neg (show ¬ leaseGrantOk (kvStateOf l lt).leases g.id g.ttl from hg)]
  case leaseRevoke =>
    dsimp only
    unfold backendTable
    rw [hk]
    dsimp only
    cases hp : rq.leaseRevoke with
    | none => rfl
    | some id =>
      simp only [Option.map_some, kvOpStep]
      by_cases hi : id ∈ lt.ids
      · rw [if_pos hi, if_pos hi, if_pos (show id ∈ (kvStateOf l lt).leases.ids from hi),
          kvStateOf_commitLog _ _ hl, hs]
        unfold KVState.commit
        split <;> rfl
      · rw [if_neg hi, if_neg hi, if_neg (show id ∉ (kvStateOf l lt).leases.ids from hi)]
  all_goals rw [hT (by rw [hk]; decide) (by rw [hk]; decide)]; try rfl

end EtcdGrove
end Perennial

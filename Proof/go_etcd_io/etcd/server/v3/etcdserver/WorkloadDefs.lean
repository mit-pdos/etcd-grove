/-
**The workload's premises, split** (D19c, option (a), 2026-10-18; `notes/decisions.md`, D19c).
Lean-first (no Rocq counterpart).

The apply thread's premise on a committed entry (`entryOk`, `InvApplier.lean`) is the txn
package's per-request premise `apply.rqOk` at the KV log the entry meets, and `dispatchOk`. The
server's construction took it for every committed log as a premise (`clusterWorkloadOk`, D13c).
Since D19c it is split in two:

* **the size clauses** (`rqSmall log rq`): room for a revision (`putOk`), the sort's small log
  (`LogSmall`). They depend on how much the cluster has written, not on the request's shape, and
  hold at every log the apply thread meets (`rqSmall_of_small`: the sole writer's log has a
  revision per non-empty change set past its first two, `txn.soleWriter`, and fewer changes than
  the time receipts' bound, `mvcc.idxCert`). (Until D19c's move, 2026-10-18, they also had fewer
  than `2 ^ 56` keys in a delete's range, a transaction's changes fewer than `2 ^ 56` and its
  gets' sorted selections small, and were a premise of the server's construction on every
  committed log, `clusterLogBound`; the store's write transaction now has them by its receipts
  as the run produces its changes, `mvcc.storeTxnWriteIs_small`.)
* **the request's shape** (`rqShape rq`): the request meets its premise at every log at which the
  size clauses hold (for a transaction: every `IgnoreValue` put finds its key unless it was
  missing at the start, every get reads revision `0` with a valid sort target and no sort cut by
  the limit, `txn.OpsIG`), and `dispatchOk` whatever the auth mode. Every proposal carries it
  (`reqPropOk`), and the KV invariant keeps it of every committed entry (`entryShape`), with the
  conf changes' id `0` (`srvCCPolicy`).

`rqOk_of_shape` puts the two back together.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Lemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.HistoryLaws
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LogLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

namespace txn

open mvcc

mutual
/-- `OpOk` by the operation's shape: a get at revision `0`, with a valid sort target, its sort
not cut by the limit; a put that needs the previous key-value finds it. (Until D19c's move,
2026-10-18, `OpOk` also had the gets' sorted selections small, `OpSort`, the size part.) -/
def OpIG (weak : Bool) (s0 : List EtcdKv) (r : w64) : List EtcdKv → TxnOp → Prop
  | _, .get o => o.base.rev = W64 0 ∧ validSortTarget o ∧ ¬ cutEarly o
  | _, .put _ _ _ => True
  | _, .delete _ => True
  | s, .putKeep k _ => IgnOk weak s0 s k
  | s, .putIgnVal k _ => IgnOk weak s0 s k
  | s, .txn cs ts es =>
    match cs.all (cmpHolds s0) with
    | true => OpsIG weak s0 r s ts
    | false => OpsIG weak s0 r s es

/-- The shape part of a run's premises. -/
def OpsIG (weak : Bool) (s0 : List EtcdKv) (r : w64) : List EtcdKv → List TxnOp → Prop
  | _, [] => True
  | s, op :: ops => OpIG weak s0 r s op ∧ OpsIG weak s0 r (applyChanges r s (srvOp s0 r s op).1) ops
end

mutual
theorem OpOk_of (weak : Bool) (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (op : TxnOp), OpIG weak s0 r s op → OpOk weak s0 r s op
  | _, .get _, h1 => h1
  | _, .put _ _ _, _ => trivial
  | _, .delete _, _ => trivial
  | _, .putKeep _ _, h1 => h1
  | _, .putIgnVal _ _, h1 => h1
  | s, .txn cs ts es, h1 => by
    simp only [OpIG, OpOk] at h1 ⊢
    split at h1 <;> split <;> simp_all <;>
      first
        | exact OpsOk_of weak s0 r s ts h1
        | exact OpsOk_of weak s0 r s es h1
        | skip

theorem OpsOk_of (weak : Bool) (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), OpsIG weak s0 r s ops → OpsOk weak s0 r s ops
  | _, [], _ => trivial
  | s, op :: ops, h1 =>
    ⟨OpOk_of weak s0 r s op h1.1, OpsOk_of weak s0 r _ ops h1.2⟩
end

/-- **A transaction's size clauses** at the log `log` (see the file header): room for a
revision, and `log` small (`LogSmall`). Until D19c's move (2026-10-18) also its changes fewer
than `2 ^ 56` and its gets' sorted selections small at the run's states, which the run now
gets from the write transaction's receipts. -/
def txnSmall (log : Log) (_t : TxnModel) : Prop :=
  log.length + 4 ≤ 2 ^ 63 ∧ LogSmall log

/-- **A transaction's shape**: the rest of its premises at every (sorted) start state and
revision. -/
def txnShape (t : TxnModel) : Prop :=
  ∀ (s0 : List EtcdKv) (r : w64), s0.Pairwise etcdKvLess →
    OpsIG true s0 r s0 (t.branch (txnOk s0 t))

theorem TxnPre_of (log : Log) (t : TxnModel) (hs : txnShape t) (hm : txnSmall log t) :
    TxnPre log t :=
  ⟨hm.1, OpsOk_of true _ _ _ _ (hs _ _ (stateAfter_sorted log)), hm.2⟩

/-! ### A transaction's shape from its run's keys -/

mutual
/-- Every get of the operation, at any depth: revision `0`, a valid sort target, no sort cut by
the limit. -/
def OpGetsOk : TxnOp → Prop
  | .get o => o.base.rev = W64 0 ∧ validSortTarget o ∧ ¬ cutEarly o
  | .txn _ ts es => OpsGetsOk ts ∧ OpsGetsOk es
  | _ => True

def OpsGetsOk : List TxnOp → Prop
  | [] => True
  | op :: ops => OpGetsOk op ∧ OpsGetsOk ops
end

mutual
/-- No get of the operation, at any depth, is a sort cut by the limit (`cutEarly`,
`issues/etcd-range-sort-none-limit.md`): a client's premise. -/
def OpNoCut : TxnOp → Prop
  | .get o => ¬ cutEarly o
  | .txn _ ts es => OpsNoCut ts ∧ OpsNoCut es
  | _ => True

def OpsNoCut : List TxnOp → Prop
  | [] => True
  | op :: ops => OpNoCut op ∧ OpsNoCut ops
end

/-- **A key present stays present** through changes that delete no key of its name. -/
theorem findKey_keep (r : w64) (k : GoString) :
    ∀ (cs : List Change) (s : List EtcdKv), s.Pairwise etcdKvLess → (findKey k s).isSome →
      k ∉ delKeysOf cs → (findKey k (applyChanges r s cs)).isSome
  | [], s, _, h, _ => h
  | c :: cs, s, hs, h, hd => by
    rw [applyChanges_cons]
    have hd' : k ∉ delKeysOf cs := fun hk => hd (by
      cases c <;> simp only [delKeysOf, List.filterMap_cons] at hk ⊢ <;>
        first | exact hk | exact List.mem_cons_of_mem _ hk)
    refine findKey_keep r k cs _ (applyChange_sorted hs r c) ?_ hd'
    cases c with
    | put k' v l =>
      show (findKey k (putKv r k' v l s)).isSome
      by_cases hk : k' = k
      · subst hk
        obtain ⟨nv, hnv, -⟩ := findKey_putKv_self hs r k' v l
        rw [hnv]; rfl
      · rw [findKey_putKv_other hs r k k' v l hk]; exact h
    | del k' =>
      show (findKey k (s.filter fun x => !decide (x.key = k'))).isSome
      have hk : k' ≠ k := fun e => hd (by simp [delKeysOf, e])
      rw [findKey_filter_ne k k' s]
      simp only [hk, ↓reduceIte]; exact h

theorem putKeysOf_app (a b : List Change) : putKeysOf (a ++ b) = putKeysOf a ++ putKeysOf b := by
  simp [putKeysOf, List.filterMap_append]

theorem delKeysOf_app (a b : List Change) : delKeysOf (a ++ b) = delKeysOf a ++ delKeysOf b := by
  simp [delKeysOf, List.filterMap_append]

/-- The run's put keys: none deleted by the run, each present at the state if at the start. -/
def KeysOk (s0 s : List EtcdKv) (cs : List Change) : Prop :=
  ∀ k ∈ putKeysOf cs, k ∉ delKeysOf cs ∧ ((findKey k s0).isSome → (findKey k s).isSome)

mutual
/-- **The shape part of an operation's premises**, from its gets' and its run's put keys (none
deleted by the run). -/
theorem opIG_of (s0 : List EtcdKv) (r : w64) :
    ∀ (op : TxnOp) (s : List EtcdKv), s.Pairwise etcdKvLess → OpGetsOk op →
      KeysOk s0 s (srvOp s0 r s op).1 → OpIG true s0 r s op
  | .get o, _, _, hg, _ => hg
  | .put _ _ _, _, _, _, _ => trivial
  | .delete _, _, _, _, _ => trivial
  | .putKeep k v, s, _, _, hk => by
    unfold KeysOk at hk
    have := (hk k (by simp [srvOp, putKeysOf])).2
    show IgnOk true s0 s k
    unfold IgnOk
    cases h0 : findKey k s0 with
    | none => exact Or.inr ⟨rfl, rfl⟩
    | some _ => exact Or.inl (this (by rw [h0]; rfl))
  | .putIgnVal k l, s, _, _, hk => by
    unfold KeysOk at hk
    have := (hk k (by simp [srvOp, putKeysOf])).2
    show IgnOk true s0 s k
    unfold IgnOk
    cases h0 : findKey k s0 with
    | none => exact Or.inr ⟨rfl, rfl⟩
    | some _ => exact Or.inl (this (by rw [h0]; rfl))
  | .txn cs ts es, s, hs, hg, hk => by
    rw [srvOp_txn] at hk
    simp only [OpIG]
    simp only [OpGetsOk] at hg
    cases hc : cs.all (cmpHolds s0) with
    | true =>
      simp only [hc, ↓reduceIte] at hk
      exact opsIG_of s0 r ts s hs hg.1 hk
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at hk
      exact opsIG_of s0 r es s hs hg.2 hk

theorem opsIG_of (s0 : List EtcdKv) (r : w64) :
    ∀ (ops : List TxnOp) (s : List EtcdKv), s.Pairwise etcdKvLess → OpsGetsOk ops →
      KeysOk s0 s (srvOps s0 r s ops).1 → OpsIG true s0 r s ops
  | [], _, _, _, _ => trivial
  | op :: ops, s, hs, hg, hk => by
    rw [srvOps_cons] at hk
    unfold KeysOk at hk
    simp only [putKeysOf_app, delKeysOf_app, List.mem_append, not_or] at hk
    refine ⟨opIG_of s0 r op s hs hg.1 ?_, opsIG_of s0 r ops _
      (applyChanges_sorted r _ hs) hg.2 ?_⟩
    · intro k h
      obtain ⟨⟨h1, -⟩, h2⟩ := hk k (Or.inl h)
      exact ⟨h1, h2⟩
    · intro k h
      obtain ⟨⟨h1, h1'⟩, h2⟩ := hk k (Or.inr h)
      exact ⟨h1', fun h0 => findKey_keep r k _ s hs (h2 h0) h1⟩
end

end txn

open go_etcd_io.etcd.server.v3.etcdserver

/-- **The size clauses of `rq`'s premise** at the log `log` (see the file header). -/
def rqSmall (log : mvcc.Log) (rq : apply.IRRModel) : Prop :=
  match apply.dispatchKind rq with
  | .put => apply.putOk log
  | .deleteRange => ∀ o, rq.deleteRange = some o → apply.delOk log o
  | .range => ∀ o, rq.range = some o → log.length + 3 ≤ 2 ^ 63 ∧ txn.sortOk o log
  | .txn => ∀ t, rq.txn = some t → txn.txnSmall log t
  | _ => True

/-- **The size clauses hold at a small log** (D19c's move, 2026-10-18): a log with a revision
per change past its first two (`txn.soleWriter`) and fewer than `2 ^ 48` changes (the time
receipts' bound, `mvcc.idxCert`, under the store's `receiptBound GF ≤ 2 ^ 48`). -/
theorem rqSmall_of_small (log : mvcc.Log) (rq : apply.IRRModel)
    (hl : log.length ≤ txn.logChanges log + 2) (hc : txn.logChanges log < 2 ^ 48) :
    rqSmall log rq := by
  have hls : txn.LogSmall log := by unfold txn.LogSmall; omega
  have h4 : log.length + 4 ≤ 2 ^ 63 := by omega
  unfold rqSmall
  split
  all_goals first
    | exact trivial
    | (unfold apply.putOk; omega)
    | (intro o _; unfold apply.delOk; omega)
    | (intro o _; exact ⟨by omega, fun _ => hls⟩)
    | (intro t _; exact ⟨h4, hls⟩)

/-- **The shape of `rq`** (see the file header): `dispatchOk` whatever the auth mode, and its
premise at every log at which the size clauses hold. -/
def rqShape (rq : apply.IRRModel) : Prop :=
  (∀ on, apply.dispatchOk on rq) ∧ ∀ log, rqSmall log rq → apply.rqOk log rq

/-- **What the KV invariant keeps of a committed entry** (D19c): a normal entry with data
decodes to a request with an id, of a good shape; a conf change has the id `0` (raft's
bootstrap's: `srvCCPolicy`). -/
def entryShape [FfiSyntax] (m : EntryModel) : Prop :=
  (m.typ = W32 0 → m.data = [] ∨ ∃ rq, apply.irrDecode m.data = some rq ∧
      (∃ id, apply.irrId rq = some id) ∧ rqShape rq) ∧
    (m.typ ≠ W32 0 → ccIdOf m.data = W64 0)

/-- Every entry of a log has a good shape. -/
def logShape [FfiSyntax] (L : List EntryModel) : Prop := ∀ m ∈ L, entryShape m

theorem logShape_append [FfiSyntax] (A B : List EntryModel) :
    logShape (A ++ B) ↔ logShape A ∧ logShape B := by
  unfold logShape
  simp only [List.mem_append]
  constructor
  · intro h; exact ⟨fun m hm => h m (Or.inl hm), fun m hm => h m (Or.inr hm)⟩
  · rintro ⟨h1, h2⟩ m (hm | hm)
    · exact h1 m hm
    · exact h2 m hm

/-- `dispatchOk` whatever the mode, of a covered request (`plainCover` excludes the compaction, the
empty request and `AuthEnable`). -/
theorem dispatchOk_of_plain (rq : apply.IRRModel) (h : plainCover rq) (on : Bool) :
    apply.dispatchOk on rq := by
  unfold plainCover at h
  unfold apply.dispatchOk
  refine ⟨?_, ?_, ?_⟩ <;> intro hk <;> rw [hk] at h <;> exact h.elim

/-- **The shape of a covered request whose premise is its size clauses** (a put, a delete, the
kinds `rqOk` asks nothing of). -/
theorem rqShape_of_plain (rq : apply.IRRModel) (h : plainCover rq)
    (hk : apply.dispatchKind rq ≠ .range ∧ apply.dispatchKind rq ≠ .txn ∧
      apply.dispatchKind rq ≠ .clusterVersionSet ∧ apply.dispatchKind rq ≠ .authUserAdd ∧
      apply.dispatchKind rq ≠ .authRoleAdd ∧ apply.dispatchKind rq ≠ .leaseCheckpoint) :
    rqShape rq := by
  refine ⟨dispatchOk_of_plain rq h, fun log hs => ?_⟩
  unfold rqSmall at hs
  unfold apply.rqOk
  unfold plainCover at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hk
  split <;> simp_all

/-- **The shape of a covered transaction request** from its transaction's shape. -/
theorem rqShape_of_txn (rq : apply.IRRModel) (h : plainCover rq)
    (hk : apply.dispatchKind rq = .txn) (ht : ∀ t, rq.txn = some t → txn.txnShape t) :
    rqShape rq := by
  refine ⟨dispatchOk_of_plain rq h, fun log hs => ?_⟩
  unfold rqSmall at hs
  unfold apply.rqOk
  rw [hk] at hs ⊢
  intro t ht'
  exact txn.TxnPre_of log t (ht t ht') (hs t ht')

end EtcdGrove
end Perennial

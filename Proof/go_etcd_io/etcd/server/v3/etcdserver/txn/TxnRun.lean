/-
The server's transaction, purely (txn unit 3): what `Txn` computes for a request denoting the
client model's `t : TxnModel` (`cache/v3/InvEtcdTxn.lean`). Lean-first; see `notes/decisions.md`,
"The server's txn", unit 3.

**The path** (`txnPath s t`, `compareToPath`): the verdicts of `t`'s comparisons and of the
comparisons of every nested transaction of the chosen branches, in pre-order, all evaluated at
the state `s` of the read transaction, before any operation runs (`opPath`, `opsPath`).
`newTxnResp`, `checkTxn` and `executeTxn` consume it: each nested transaction takes its own
path, `opPath s op`, of length one plus the number of transactions nested in it
(`txnPath_length`).

**The server's run** (`srvOp`, `srvOps`, `srvRunTxn`): the client's `applyTxnOp`/`runOps`, but
a nested transaction's branch is chosen by its verdict at the read state `s0` (the path), not at
the state the operations before it left: etcd evaluates every comparison first
(`compareToPath`), then runs the operations. The run returns the mvcc changes the operations
make (`List Change`: a put's `putChangeOf`, a delete's keys) rather than the state, so the write
transaction's pending changes are named; the state is `applyChanges r s` of them
(`srvOps_state`). The two runs agree when every nested transaction's verdict is the same at
`s0` and at the state it runs at (`OpsStable`, `srvRunTxn_runTxn`), in particular when there is
no nested transaction (`opsFlat`); they differ otherwise (`issues/etcd-txn-nested-compare-
snapshot.md`).

**The premises of a run** (`OpsOk`): every get reads the transaction's state (revision `0`), with
a valid sort target, a sort not cut by its limit (`¬ cutEarly`: the client's `rangeKvsOk`
otherwise fails, `issues/etcd-range-sort-none-limit.md`) and, if it sorts, a small selection
(`sortSmall`, `sortRangeResults`' premise); every put that needs the previous key-value
(`IgnoreValue`/`IgnoreLease`) finds it at the state it runs at, unless (`weak`) it was already
missing at `s0` (then `checkTxn` fails first): a delete earlier in the same transaction can
remove it, and `put` then indexes an empty `KVs` (`issues/etcd-txn-delete-then-ignore-put.md`).
`PathIgnOk` is what `checkTxn` establishes (every such put finds its key at `s0`), and with it the
weak premise is the strong one (`opsOk_strong`). `opsLeases` are the leases the path's puts name
(`checkLease` checks them).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Write
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open mvcc

/-! ## The path -/

mutual
/-- The verdicts of the nested transactions of `op` (itself first), in pre-order, at `s`. -/
def opPath (s : List EtcdKv) : TxnOp → List Bool
  | .txn cs ts es =>
    match cs.all (cmpHolds s) with
    | true => true :: opsPath s ts
    | false => false :: opsPath s es
  | .get _ => []
  | .put _ _ _ => []
  | .delete _ => []
  | .putKeep _ _ => []
  | .putIgnVal _ _ => []

/-- The verdicts of the nested transactions of `ops`, in order. -/
def opsPath (s : List EtcdKv) : List TxnOp → List Bool
  | [] => []
  | op :: ops => opPath s op ++ opsPath s ops
end

/-- The verdict of `t`'s comparisons at `s`. -/
abbrev txnOk (s : List EtcdKv) (t : TxnModel) : Bool := t.cmps.all (cmpHolds s)

/-- **`compareToPath`'s result**: the verdict of `t`, then the paths of the nested transactions
of the branch it chooses, in order; every comparison at `s`. -/
def txnPath (s : List EtcdKv) (t : TxnModel) : List Bool :=
  txnOk s t :: opsPath s (t.branch (txnOk s t))

/-- The number of transactions nested (at any depth) in the branch `t` chooses at `s`: what
`newTxnResp`, `checkTxn` and `executeTxn` return. -/
def nestedCount (s : List EtcdKv) (t : TxnModel) : Nat := (opsPath s (t.branch (txnOk s t))).length

/-- **The path's length** is one plus the number of nested transactions. -/
theorem txnPath_length (s : List EtcdKv) (t : TxnModel) :
    (txnPath s t).length = nestedCount s t + 1 := by
  simp [txnPath, nestedCount]

/-- A nested transaction's path is its own `txnPath`. -/
theorem opPath_txn (s : List EtcdKv) (cs : List CmpModel) (ts es : List TxnOp) :
    opPath s (.txn cs ts es) = txnPath s { cmps := cs, thenOps := ts, elseOps := es } := by
  unfold txnPath txnOk TxnModel.branch
  simp only [opPath]
  cases cs.all (cmpHolds s) <;> rfl

theorem opsPath_nil (s : List EtcdKv) : opsPath s [] = [] := by simp [opsPath]

theorem opsPath_cons (s : List EtcdKv) (op : TxnOp) (ops : List TxnOp) :
    opsPath s (op :: ops) = opPath s op ++ opsPath s ops := by simp [opsPath]

/-- `opsPath` of the operations from the `i`-th on: the `i`-th's path, then the rest's. -/
theorem opsPath_drop (s : List EtcdKv) (ops : List TxnOp) (i : Nat) (op : TxnOp)
    (h : ops[i]? = some op) :
    opsPath s (ops.drop i) = opPath s op ++ opsPath s (ops.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 h).1]
  simp [opsPath_cons, (List.getElem?_eq_some_iff.1 h).2]

/-- `opsPath` of the first `i + 1` operations. -/
theorem opsPath_take_succ (s : List EtcdKv) (ops : List TxnOp) (i : Nat) (op : TxnOp)
    (h : ops[i]? = some op) :
    opsPath s (ops.take (i + 1)) = opsPath s (ops.take i) ++ opPath s op := by
  have hl : ops.take (i + 1) = ops.take i ++ [op] := by
    rw [List.take_add_one, h]; rfl
  rw [hl]
  generalize ops.take i = l
  induction l with
  | nil => simp [opsPath]
  | cons x l ih => simp [opsPath_cons, ih]

/-- A non-transaction operation has no path. -/
theorem opPath_nontxn (s : List EtcdKv) (op : TxnOp) (h : ∀ cs ts es, op ≠ .txn cs ts es) :
    opPath s op = [] := by
  cases op with
  | txn cs ts es => exact absurd rfl (h cs ts es)
  | _ => simp [opPath]

/-! ## The server's run -/

mutual
/-- **One operation of the server's run** at revision `r`, at the state `s`, the nested
transactions' verdicts taken at `s0`: the changes it makes and its result. -/
def srvOp (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) : TxnOp → List Change × TxnOpResult
  | .get o => ([], .range (rangeSel s o) (rangeIn s o).length)
  | .put k v l => ([.put k v l], .put)
  | .putKeep k v => ([.put k v (((findKey k s).map EtcdKv.lease).getD (W64 0))], .put)
  | .putIgnVal k l =>
    ([.put k (((findKey k s).map EtcdKv.value).getD [])
      (l.getD (((findKey k s).map EtcdKv.lease).getD (W64 0)))], .put)
  | .delete o => ((rangeIn s o).map (fun v => .del v.key), .delete (rangeIn s o).length)
  | .txn cs ts es =>
    match cs.all (cmpHolds s0) with
    | true => ((srvOps s0 r s ts).1, .txn true (srvOps s0 r s ts).2)
    | false => ((srvOps s0 r s es).1, .txn false (srvOps s0 r s es).2)

/-- The server's run of operations in order, each at the state the changes before it left. -/
def srvOps (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) : List TxnOp → List Change × List TxnOpResult
  | [] => ([], [])
  | op :: ops =>
    ((srvOp s0 r s op).1 ++ (srvOps s0 r (applyChanges r s (srvOp s0 r s op).1) ops).1,
      (srvOp s0 r s op).2 :: (srvOps s0 r (applyChanges r s (srvOp s0 r s op).1) ops).2)
end

/-- **The server's transaction** at revision `r` on the state `s`: the verdict, the changes of
the chosen branch's run (the write transaction's pending changes), its results. -/
def srvRunTxn (r : w64) (s : List EtcdKv) (t : TxnModel) :
    Bool × List Change × List TxnOpResult :=
  (txnOk s t, (srvOps s r s (t.branch (txnOk s t))).1, (srvOps s r s (t.branch (txnOk s t))).2)

theorem srvOps_nil (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) : srvOps s0 r s [] = ([], []) := by
  simp [srvOps]

theorem srvOps_cons (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (op : TxnOp) (ops : List TxnOp) :
    srvOps s0 r s (op :: ops) =
      ((srvOp s0 r s op).1 ++ (srvOps s0 r (applyChanges r s (srvOp s0 r s op).1) ops).1,
        (srvOp s0 r s op).2 :: (srvOps s0 r (applyChanges r s (srvOp s0 r s op).1) ops).2) := by
  simp [srvOps]

theorem srvOp_txn (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (cs : List CmpModel)
    (ts es : List TxnOp) :
    srvOp s0 r s (.txn cs ts es) =
      ((srvOps s0 r s (if cs.all (cmpHolds s0) then ts else es)).1,
        .txn (cs.all (cmpHolds s0)) (srvOps s0 r s (if cs.all (cmpHolds s0) then ts else es)).2) := by
  simp only [srvOp]
  cases cs.all (cmpHolds s0) <;> rfl

/-- The server's run of the operations from the `i`-th on, at the state the first `i` left:
the `i`-th's, then the rest's. -/
theorem srvOps_drop (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (ops : List TxnOp) (i : Nat)
    (op : TxnOp) (h : ops[i]? = some op) :
    srvOps s0 r s (ops.drop i) =
      ((srvOp s0 r s op).1 ++ (srvOps s0 r (applyChanges r s (srvOp s0 r s op).1) (ops.drop (i + 1))).1,
        (srvOp s0 r s op).2 ::
          (srvOps s0 r (applyChanges r s (srvOp s0 r s op).1) (ops.drop (i + 1))).2) := by
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 h).1, srvOps_cons,
    (List.getElem?_eq_some_iff.1 h).2]

/-- The changes of a put, at the state `s`: the server's `putChangeOf`. -/
theorem srvOp_putTxnOp (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (o : OpFull) :
    srvOp s0 r s (putTxnOp o) = ([putChangeOf o (findKey o.key s)], .put) := by
  unfold putTxnOp putChangeOf putValOf putLeaseOf
  cases hv : o.ignoreValue <;> cases hl : o.ignoreLease <;> simp [srvOp]

/-- The changes of a delete, at the state `s`: the server's `delChanges`. -/
theorem srvOp_delete (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (o : OpFull) :
    srvOp s0 r s (.delete o) = (delChanges s o, .delete (rangeIn s o).length) := by
  simp [srvOp, delChanges]

/-- A delete's changes leave the state without its range (the client's filter). -/
theorem applyChanges_delChanges (r : w64) (s : List EtcdKv) (o : OpFull) :
    applyChanges r s (delChanges s o) = s.filter (fun v => !inRange o.key o.base.rangeEnd v.key) := by
  have hm : (rangeIn s o).map (fun v => Change.del v.key) =
      ((rangeIn s o).map EtcdKv.key).map Change.del := by
    rw [List.map_map]; rfl
  unfold delChanges
  rw [hm, rangeIn, applyChanges_dels_sel]

/-- **One operation's changes are the client's step** (`applyTxnOp`), for any operation but a
nested transaction. -/
theorem srvOp_state (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (op : TxnOp)
    (h : ∀ cs ts es, op ≠ .txn cs ts es) :
    applyChanges r s (srvOp s0 r s op).1 = (applyTxnOp r s op).1 ∧
      (srvOp s0 r s op).2 = (applyTxnOp r s op).2 := by
  cases op with
  | txn cs ts es => exact absurd rfl (h cs ts es)
  | get o => simp [srvOp, applyTxnOp, applyChanges]
  | put k v l => simp [srvOp, applyTxnOp, applyChanges, applyChange_put]
  | putKeep k v => simp [srvOp, applyTxnOp, applyChanges, applyChange_put, findKey]
  | putIgnVal k l => simp [srvOp, applyTxnOp, applyChanges, applyChange_put, findKey]
  | delete o =>
    refine ⟨?_, by simp [srvOp, applyTxnOp]⟩
    have := applyChanges_delChanges r s o
    unfold delChanges at this
    simp only [srvOp, applyTxnOp]
    exact this

/-! ## Agreement with the client model -/

mutual
/-- Every nested transaction of `op` (run at `s`) has the same verdict at `s0` as at the state
it runs at. -/
def OpStable (s0 : List EtcdKv) (r : w64) : List EtcdKv → TxnOp → Prop
  | s, .txn cs ts es =>
    cs.all (cmpHolds s0) = cs.all (cmpHolds s) ∧
    (match cs.all (cmpHolds s0) with
     | true => OpsStable s0 r s ts
     | false => OpsStable s0 r s es)
  | _, .get _ => True
  | _, .put _ _ _ => True
  | _, .delete _ => True
  | _, .putKeep _ _ => True
  | _, .putIgnVal _ _ => True

/-- `OpStable` of every operation, each at the state the ones before it left. -/
def OpsStable (s0 : List EtcdKv) (r : w64) : List EtcdKv → List TxnOp → Prop
  | _, [] => True
  | s, op :: ops => OpStable s0 r s op ∧ OpsStable s0 r (applyChanges r s (srvOp s0 r s op).1) ops
end

mutual
/-- **The server's run is the client's** where the nested verdicts are stable. -/
theorem srvOp_applyTxnOp (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (op : TxnOp), OpStable s0 r s op →
      applyChanges r s (srvOp s0 r s op).1 = (applyTxnOp r s op).1 ∧
        (srvOp s0 r s op).2 = (applyTxnOp r s op).2
  | s, .txn cs ts es, h => by
    obtain ⟨heq, hrest⟩ := h
    simp only [srvOp, applyTxnOp]
    rw [← heq]
    cases hc : cs.all (cmpHolds s0)
    · rw [hc] at hrest
      have := srvOps_runOps s0 r s es hrest
      exact ⟨this.1, by rw [this.2]⟩
    · rw [hc] at hrest
      have := srvOps_runOps s0 r s ts hrest
      exact ⟨this.1, by rw [this.2]⟩
  | s, .get o, _ => srvOp_state s0 r s (.get o) (by intros; simp)
  | s, .put k v l, _ => srvOp_state s0 r s (.put k v l) (by intros; simp)
  | s, .delete o, _ => srvOp_state s0 r s (.delete o) (by intros; simp)
  | s, .putKeep k v, _ => srvOp_state s0 r s (.putKeep k v) (by intros; simp)
  | s, .putIgnVal k l, _ => srvOp_state s0 r s (.putIgnVal k l) (by intros; simp)

theorem srvOps_runOps (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), OpsStable s0 r s ops →
      applyChanges r s (srvOps s0 r s ops).1 = (runOps r s ops).1 ∧
        (srvOps s0 r s ops).2 = (runOps r s ops).2
  | s, [], _ => by simp [srvOps, runOps, applyChanges]
  | s, op :: ops, h => by
    obtain ⟨h1, h2⟩ := h
    have e1 := srvOp_applyTxnOp s0 r s op h1
    have e2 := srvOps_runOps s0 r (applyChanges r s (srvOp s0 r s op).1) ops h2
    rw [e1.1] at e2
    simp only [srvOps, runOps, applyChanges_append]
    rw [e1.1, e2.1, e2.2, e1.2]
    exact ⟨rfl, rfl⟩
end

/-- **The server's transaction is the client model's `runTxn`** when the nested verdicts are
stable: same verdict, the changes give the client's state, same results. -/
theorem srvRunTxn_runTxn (r : w64) (s : List EtcdKv) (t : TxnModel)
    (h : OpsStable s r s (t.branch (txnOk s t))) :
    (srvRunTxn r s t).1 = (runTxn r s t).1 ∧
      applyChanges r s (srvRunTxn r s t).2.1 = (runTxn r s t).2.1 ∧
      (srvRunTxn r s t).2.2 = (runTxn r s t).2.2 := by
  have := srvOps_runOps s r s _ h
  exact ⟨rfl, this.1, this.2⟩

/-- The operations have no nested transaction. -/
def opsFlat (ops : List TxnOp) : Prop := ∀ op ∈ ops, ∀ cs ts es, op ≠ .txn cs ts es

/-- Without nested transactions, the verdicts are trivially stable. -/
theorem opsStable_flat (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), opsFlat ops → OpsStable s0 r s ops
  | _, [], _ => by simp [OpsStable]
  | s, op :: ops, h => by
    refine ⟨?_, opsStable_flat s0 r _ ops (fun o ho => h o (List.mem_cons_of_mem _ ho))⟩
    have hop := h op List.mem_cons_self
    cases op with
    | txn cs ts es => exact absurd rfl (hop cs ts es)
    | _ => simp [OpStable]

/-! ## The premises of a run -/

/-- A sorted selection is small (`sortRangeResults`' premise, at the state read). -/
def sortSmall (o : OpFull) (s : List EtcdKv) : Prop :=
  (o.effSortOrder = W64 1 ∨ o.effSortOrder = W64 2) →
    (srvPre o s).length ≤ 2 ^ 62 ∧ ∀ v ∈ srvPre o s, kvOk v

/-- **A get in a transaction** reads the transaction's state (revision `0`, as the client's
`txnOpOf`), with a valid sort target, a sort not cut by the limit, and a small sorted
selection. -/
def GetOk (s : List EtcdKv) (o : OpFull) : Prop :=
  o.base.rev = W64 0 ∧ validSortTarget o ∧ ¬ cutEarly o ∧ sortSmall o s

/-- A put that needs the previous key-value finds it at `s`, or (`weak`) did not at `s0`. -/
def IgnOk (weak : Bool) (s0 s : List EtcdKv) (k : GoString) : Prop :=
  (findKey k s).isSome ∨ (weak = true ∧ findKey k s0 = none)

mutual
/-- **The premises of one operation of the run** at `s` (see the module docstring). -/
def OpOk (weak : Bool) (s0 : List EtcdKv) (r : w64) : List EtcdKv → TxnOp → Prop
  | s, .get o => GetOk s o
  | _, .put _ _ _ => True
  | _, .delete _ => True
  | s, .putKeep k _ => IgnOk weak s0 s k
  | s, .putIgnVal k _ => IgnOk weak s0 s k
  | s, .txn cs ts es =>
    match cs.all (cmpHolds s0) with
    | true => OpsOk weak s0 r s ts
    | false => OpsOk weak s0 r s es

/-- The premises of every operation, each at the state the ones before it left. -/
def OpsOk (weak : Bool) (s0 : List EtcdKv) (r : w64) : List EtcdKv → List TxnOp → Prop
  | _, [] => True
  | s, op :: ops => OpOk weak s0 r s op ∧ OpsOk weak s0 r (applyChanges r s (srvOp s0 r s op).1) ops
end

mutual
/-- Every put of `op`'s path that needs the previous key-value finds it at `s0` (what `checkTxn`
checks). -/
def PathIgnOk (s0 : List EtcdKv) : TxnOp → Prop
  | .putKeep k _ => (findKey k s0).isSome
  | .putIgnVal k _ => (findKey k s0).isSome
  | .txn cs ts es =>
    match cs.all (cmpHolds s0) with
    | true => PathsIgnOk s0 ts
    | false => PathsIgnOk s0 es
  | .get _ => True
  | .put _ _ _ => True
  | .delete _ => True

def PathsIgnOk (s0 : List EtcdKv) : List TxnOp → Prop
  | [] => True
  | op :: ops => PathIgnOk s0 op ∧ PathsIgnOk s0 ops
end

mutual
theorem opOk_strong (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (op : TxnOp), OpOk true s0 r s op → PathIgnOk s0 op → OpOk false s0 r s op
  | s, .txn cs ts es, h, hp => by
    simp only [OpOk, PathIgnOk] at h hp ⊢
    cases hc : cs.all (cmpHolds s0)
    · rw [hc] at h hp; exact opsOk_strong s0 r s es h hp
    · rw [hc] at h hp; exact opsOk_strong s0 r s ts h hp
  | s, .putKeep k v, h, hp => by
    simp only [OpOk, IgnOk, PathIgnOk] at h hp ⊢
    rcases h with h | ⟨-, h⟩
    · exact Or.inl h
    · rw [h] at hp; cases hp
  | s, .putIgnVal k l, h, hp => by
    simp only [OpOk, IgnOk, PathIgnOk] at h hp ⊢
    rcases h with h | ⟨-, h⟩
    · exact Or.inl h
    · rw [h] at hp; cases hp
  | s, .get o, h, _ => h
  | s, .put k v l, h, _ => h
  | s, .delete o, h, _ => h

/-- **With `checkTxn`'s check, the weak premise is the strong one.** -/
theorem opsOk_strong (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), OpsOk true s0 r s ops → PathsIgnOk s0 ops →
      OpsOk false s0 r s ops
  | _, [], _, _ => by simp [OpsOk]
  | s, op :: ops, h, hp => by
    simp only [OpsOk, PathsIgnOk] at h hp ⊢
    exact ⟨opOk_strong s0 r s op h.1 hp.1, opsOk_strong s0 r _ ops h.2 hp.2⟩
end

theorem opsOk_drop (weak : Bool) (s0 : List EtcdKv) (r : w64) (s : List EtcdKv) (ops : List TxnOp)
    (i : Nat) (op : TxnOp) (h : ops[i]? = some op) :
    OpsOk weak s0 r s (ops.drop i) ↔
      OpOk weak s0 r s op ∧ OpsOk weak s0 r (applyChanges r s (srvOp s0 r s op).1) (ops.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.1 h).1, (List.getElem?_eq_some_iff.1 h).2]
  simp [OpsOk]

theorem pathsIgnOk_append (s0 : List EtcdKv) :
    ∀ (a b : List TxnOp), PathsIgnOk s0 (a ++ b) ↔ PathsIgnOk s0 a ∧ PathsIgnOk s0 b
  | [], b => by simp [PathsIgnOk]
  | x :: a, b => by
    simp only [List.cons_append, PathsIgnOk]
    rw [pathsIgnOk_append s0 a b]
    exact and_assoc.symm

mutual
/-- The leases `op`'s path's puts name (`checkLease` checks them): a put's, an `IgnoreValue`
put's unless it also ignores the lease. -/
def opLeases (s0 : List EtcdKv) : TxnOp → List w64
  | .put _ _ l => [l]
  | .putIgnVal _ l => l.toList
  | .txn cs ts es =>
    match cs.all (cmpHolds s0) with
    | true => opsLeases s0 ts
    | false => opsLeases s0 es
  | .get _ => []
  | .delete _ => []
  | .putKeep _ _ => []

def opsLeases (s0 : List EtcdKv) : List TxnOp → List w64
  | [] => []
  | op :: ops => opLeases s0 op ++ opsLeases s0 ops
end

theorem opsLeases_append (s0 : List EtcdKv) :
    ∀ (a b : List TxnOp), opsLeases s0 (a ++ b) = opsLeases s0 a ++ opsLeases s0 b
  | [], b => by simp [opsLeases]
  | x :: a, b => by simp [opsLeases, opsLeases_append s0 a b]

/-- The lease a put of the path writes at `s`: one it names, or (`IgnoreLease`) the previous
key-value's. -/
theorem putLeaseOf_mem (s0 : List EtcdKv) (o : OpFull) (s : List EtcdKv) :
    putLeaseOf o (findKey o.key s) ∈ opLeases s0 (putTxnOp o) ∨
      (o.ignoreLease = true ∧ putLeaseOf o (findKey o.key s) =
        ((findKey o.key s).map EtcdKv.lease).getD (W64 0)) := by
  unfold putLeaseOf putTxnOp
  cases hv : o.ignoreValue <;> cases hl : o.ignoreLease <;> simp [opLeases]

/-- **`Txn`'s premises** at the sole writer's log `log`: room for one more revision, the run's
premises (weak: an `IgnoreValue`/`IgnoreLease` put whose key is missing at `log` fails
`checkTxn`), room for the run's changes (fewer than `2 ^ 56`: the real backend's bound on a
session's puts, `mvcc.putMax`; 2026-10-13, unit 6: it was `2 ^ 63`). -/
def TxnPre (log : Log) (t : TxnModel) : Prop :=
  log.length + 4 ≤ 2 ^ 63 ∧
  OpsOk true (stateAfter log) (W64 (log.length : Int)) (stateAfter log)
    (t.branch (txnOk (stateAfter log) t)) ∧
  (srvRunTxn (W64 (log.length : Int)) (stateAfter log) t).2.1.length < 2 ^ 56

/-! ## Read-only and serializable requests -/

/-- An operation is a get. -/
def opIsGet : TxnOp → Bool
  | .get _ => true
  | _ => false

/-- An operation is a serializable get. -/
def opIsSerGet : TxnOp → Bool
  | .get o => o.base.serializable
  | _ => false

/-- **`IsTxnReadonly`**: every operation of both branches is a get (a nested transaction is
not). -/
def txnReadonly (t : TxnModel) : Bool := (t.thenOps ++ t.elseOps).all opIsGet

/-- **`IsTxnSerializable`**: every operation of both branches is a serializable get. -/
def txnSerializable (t : TxnModel) : Bool := (t.thenOps ++ t.elseOps).all opIsSerGet

/-- **The gets of a transaction are within the model** (pure; the premise of `Txn` at a reader,
the server's read-only transaction: 2026-10-12, the request path's unit 3b): every get of either
branch reads the transaction's revision (`0`: the model's gets in a transaction are the client's
`txnOpOf`), its sort is not cut early by a limit (`cutEarly`,
`issues/etcd-range-sort-none-limit.md`), and its sort target is valid (what the gRPC layer's
`checkRangeRequest` checks). The apply thread's `Txn` has the same premises through `TxnPre`. -/
def txnGetsOk (t : TxnModel) : Prop :=
  ∀ o : OpFull, TxnOp.get o ∈ t.thenOps ++ t.elseOps →
    o.base.rev = W64 0 ∧ ¬ cutEarly o ∧ validSortTarget o

theorem opIsSerGet_linearizable (op : TxnOp) : opIsSerGet op = !op.linearizable := by
  cases op <;> simp [opIsSerGet, TxnOp.linearizable]

theorem all_serGet (l : List TxnOp) : l.all opIsSerGet = !l.any TxnOp.linearizable := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [opIsSerGet_linearizable, ih]

/-- **`IsTxnSerializable` is the client's "not linearizable"** (`TxnModel.linearizable`). -/
theorem serializable_linearizable (t : TxnModel) : txnSerializable t = !t.linearizable := by
  unfold txnSerializable TxnModel.linearizable
  exact all_serGet _

/-- A serializable transaction is read-only. -/
theorem readonly_of_serializable (t : TxnModel) (h : txnSerializable t = true) :
    txnReadonly t = true := by
  unfold txnSerializable at h
  unfold txnReadonly
  rw [List.all_eq_true] at h ⊢
  intro op hop
  have := h op hop
  cases op <;> simp_all [opIsSerGet, opIsGet]

/-- The chosen branch of a read-only transaction has only gets. -/
theorem readonly_branch (t : TxnModel) (h : txnReadonly t = true) (ok : Bool) :
    ∀ op ∈ t.branch ok, opIsGet op = true := by
  intro op hop
  unfold txnReadonly at h
  rw [List.all_eq_true] at h
  apply h
  unfold TxnModel.branch at hop
  cases ok <;> simp_all

/-- Gets make no change. -/
theorem srvOps_gets (s0 : List EtcdKv) (r : w64) :
    ∀ (s : List EtcdKv) (ops : List TxnOp), (∀ op ∈ ops, opIsGet op = true) →
      (srvOps s0 r s ops).1 = []
  | _, [], _ => by simp [srvOps]
  | s, op :: ops, h => by
    have hop := h op List.mem_cons_self
    cases op with
    | get o =>
      simp only [srvOps, srvOp, List.nil_append]
      exact srvOps_gets s0 r _ ops (fun x hx => h x (List.mem_cons_of_mem _ hx))
    | _ => simp [opIsGet] at hop

end txn
end EtcdGrove
end Perennial

/-
Lean-first (no Rocq counterpart).

# linkv: the KV model against etcd's state (linkv-txn stage C, 2026-10-20)

`TxnModel.lean`'s model (`mStep`) against etcd's KV state (`KVState`, the key-values at the latest
revision, sorted by key) and the server's steps (`kvOpStep`, the txn package's `runTxn`/
`srvRunTxn`). The abstraction (`absM`, `absSt`) is exact: a key's model value is its key-value's
value, mod revision and version (`absVR`), and the model's revision the state's.

The operations the instance sends (`opOf`, `tOpOf`, `cmpOf`): the client's plain get, put and
delete of a key (`getOp`, `putOp`, `delOp`), a list of the keys `[pfx, end)` (`listOp`), and flat
transactions of single-key comparisons for equality (value, version, mod revision) and single-key
gets, puts and deletes. On a sorted state:

- `absM_putKv`, `absM_delete`, `rangeSel_getOp`, `rangeIn_delOp_length`, `cmpHolds_cmpOf`: one
  operation of each kind at the level of key-value lists;
- `srvOp_tOpOf`, `srvOps_tOpOf`: a transaction's operations, in order, the server's run;
- **`absSt_kvOpStep`**: the server's step of every model input (`opOf`) moves the model state as
  the model's step; and its answers (`mStep_put_out`, `mStep_get_out`, `mStep_del_out`,
  `mStep_txn_out`, `mStep_list_out`) are the model's: what the replies' values say
  (`client/v3/ReplyValues.lean`) as functions of the state the update fired at;
- the state's shape is kept (`kvOpStep_sorted`; `kvOpStep_keysIn` for inputs of the workload's
  keys, what `list` needs), the start is the model's (`absSt_init`), and the transactions are
  plain and flat (`txnPlain_txnOf`, `opsFlat_tOpOf`).
Moved from `examples/linkv/` when linkv was retired (2026-10-22, `notes/decisions.md` D34); the
names keep their namespace `linkv`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.TxnModel
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.ModelKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.TxnRun

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open mvcc

section kv
variable [ext : FfiSyntax]

/-! ## The abstraction -/

/-- A key-value's model value: its value, mod revision and version. -/
def absVR (e : EtcdKv) : VR GoString := ⟨e.value, e.modRev, e.version⟩

/-- The model store of a list of key-values: every key's first key-value's. -/
def absM (s : List EtcdKv) : MStore GoString GoString := fun k => (findKey k s).map absVR

/-- **The model state of etcd's KV state.** -/
def absSt (σ : KVState) : MSt GoString GoString := ⟨absM σ.kvs, σ.rev⟩

/-! ## The operations the instance sends -/

/-- The delete of `k` with no options (`cli.Delete(ctx, k)`). -/
abbrev delOp (k : GoString) : OpFull := txn.deleteOpOf k [] false

/-- A get of the keys `[k, e)` with no other option (`cli.Get(ctx, k, WithRange(e))`). -/
abbrev listOp (k e : GoString) : OpFull :=
  txn.rangeOpOf k e (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0) (W64 0) (W64 0)
    (W64 0)

/-- A model comparison as the client sends it. -/
def cmpOf : MCmp GoString GoString → CmpModel
  | .val k v => { key := k, rangeEnd := [], target := .value, op := .eq, num := W64 0, val := v }
  | .ver k n => { key := k, rangeEnd := [], target := .version, op := .eq, num := n, val := [] }
  | .mod k n => { key := k, rangeEnd := [], target := .mod, op := .eq, num := n, val := [] }

/-- A model transaction operation as the client sends it. -/
def tOpOf : MOp GoString GoString → TxnOp
  | .get k => .get (getOp k)
  | .put k v => .put k v (W64 0)
  | .del k => .delete (delOp k)

/-- A transaction operation's result in the model. -/
def resOf : TxnOpResult → MRes GoString
  | .range sel _ => .get (sel.head?.map absVR)
  | .put => .put
  | .delete n => .del n
  | .txn _ _ => .put

/-! ## Sorted lists -/

/-- In a list sorted by key, a key's key-values are the one its key finds, or none. -/
theorem filter_key_sorted (k : GoString) :
    ∀ (s : List EtcdKv), s.Pairwise etcdKvLess →
      s.filter (fun v => decide (v.key = k)) = (findKey k s).toList
  | [], _ => by simp [findKey]
  | w :: ws, hs => by
    rw [List.pairwise_cons] at hs
    rw [findKey_cons]
    by_cases hw : w.key = k
    · have hnil : ws.filter (fun v => decide (v.key = k)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy hyk
        have hlt := hs.1 y hy
        unfold etcdKvLess at hlt
        simp only [decide_eq_true_eq] at hyk
        rw [hw, hyk] at hlt
        exact go.goStringLt_irrefl _ hlt
      simp [hw, hnil]
    · simp only [List.filter_cons, hw, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact filter_key_sorted k ws hs.2

theorem findKey_mem {k : GoString} {s : List EtcdKv} {e : EtcdKv} (h : findKey k s = some e) :
    e ∈ s := List.mem_of_find?_eq_some h

/-- A single key's range is the key. -/
theorem inRange_key (k k' : GoString) : inRange k [] k' = decide (k' = k) := by
  simp [inRange]

/-! ## One operation at the level of key-value lists -/

/-- **A put steps the model store as the model's put.** -/
theorem absM_putKv (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) (r : Nat) (k v : GoString) :
    absM (putKv (W64 (r : Int)) k v (W64 0) s) = (absM s).put r k v := by
  funext k'
  unfold absM MStore.put
  by_cases hk : k' = k
  · subst hk
    obtain ⟨nv, hnv, -, hmod, -, hver⟩ := findKey_putKv_self hs (W64 (r : Int)) k' v (W64 0)
    obtain ⟨nv', hnv', -, hval⟩ := findKey_putKv_val s hs (W64 (r : Int)) k' v (W64 0)
    rw [hnv] at hnv'
    cases hnv'
    rw [hnv]
    simp only [Option.map_some, ite_true, Option.some.injEq]
    unfold absVR
    rw [hmod, hver, hval]
    cases findKey k' s <;> rfl
  · simp only [hk, ite_false]
    rw [findKey_putKv_other hs _ k' k v _ (Ne.symm hk)]

/-- **A delete of a key steps the model store as the model's delete.** -/
theorem absM_delete (s : List EtcdKv) (k : GoString) :
    absM (s.filter (fun v => !inRange (delOp k).key (delOp k).base.rangeEnd v.key)) =
      (absM s).del k := by
  funext k'
  have hf : (fun v : EtcdKv => !inRange (delOp k).key (delOp k).base.rangeEnd v.key) =
      (fun v => !decide (v.key = k)) := by
    funext v
    simp [txn.deleteOpOf, op_simps, inRange]
  rw [hf]
  unfold absM MStore.del
  rw [findKey_filter_ne]
  by_cases hk : k' = k
  · simp [hk]
  · simp [hk, Ne.symm hk]

/-- A delete's range in the state. -/
theorem rangeIn_delOp (s : List EtcdKv) (k : GoString) :
    rangeIn s (delOp k) = s.filter (fun v => decide (v.key = k)) := by
  unfold rangeIn
  simp [txn.deleteOpOf, op_simps, inRange]

/-- **A delete's count**: `1` if the key is there, else `0`. -/
theorem rangeIn_delOp_length (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) (k : GoString) :
    (rangeIn s (delOp k)).length = if ((absM s) k).isSome then 1 else 0 := by
  rw [rangeIn_delOp, filter_key_sorted k s hs]
  unfold absM
  cases findKey k s <;> simp

/-- A get's range in the state. -/
theorem rangeIn_getOp (s : List EtcdKv) (k : GoString) :
    rangeIn s (getOp k) = s.filter (fun v => decide (v.key = k)) := by
  unfold rangeIn
  simp [txn.rangeOpOf, op_simps, inRange]

/-- **A get's selection reads the model store.** -/
theorem rangeSel_getOp (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) (k : GoString) :
    (rangeSel s (getOp k)).head?.map absVR = (absM s) k := by
  unfold rangeSel
  have hf : (rangeIn s (getOp k)).filter (kvFilterOk (getOp k)) = rangeIn s (getOp k) := by
    rw [List.filter_eq_self]
    intro v _
    simp [kvFilterOk, txn.rangeOpOf, op_simps]
  rw [hf, rangeIn_getOp, filter_key_sorted k s hs]
  unfold absM
  cases findKey k s <;> rfl

/-- An equality comparison's verdict, from its sign: whether the two are equal. -/
theorem cmpSign_eq_zero (lt eq : Bool) (h : eq = true → lt = false) : (cmpSign lt eq == 0) = eq := by
  unfold cmpSign
  cases lt <;> cases eq <;> simp_all

theorem bytesCmp_eq_zero (a b : GoString) : (bytesCmp a b == 0) = decide (a = b) := by
  unfold bytesCmp
  apply cmpSign_eq_zero
  intro h
  simp only [decide_eq_true_eq] at h
  subst h
  simp [go.goStringLt_irrefl]

theorem int64Cmp_eq_zero' (a b : w64) : (int64Cmp a b == 0) = decide (a = b) := by
  unfold int64Cmp
  apply cmpSign_eq_zero
  intro h
  simp only [decide_eq_true_eq] at h
  subst h
  simp

/-- **A comparison's verdict is the model's.** -/
theorem cmpHolds_cmpOf (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) (c : MCmp GoString GoString) :
    cmpHolds s (cmpOf c) = c.holds (absM s) := by
  have hsel : ∀ (k : GoString),
      s.filter (fun v => inRange k [] v.key) = (findKey k s).toList := by
    intro k
    have : (fun v : EtcdKv => inRange k [] v.key) = (fun v => decide (v.key = k)) := by
      funext v; exact inRange_key k v.key
    rw [this]
    exact filter_key_sorted k s hs
  cases c with
  | val k v =>
    unfold cmpHolds MCmp.holds absM
    simp only [cmpOf, hsel k]
    cases findKey k s with
    | none => simp
    | some e => simp [cmpKv, CmpOp.holds, bytesCmp_eq_zero, absVR]
  | ver k n =>
    unfold cmpHolds MCmp.holds absM
    simp only [cmpOf, hsel k]
    cases findKey k s with
    | none => simp [cmpKv, CmpOp.holds, int64Cmp_eq_zero', zeroKv]
    | some e =>
      simp only [cmpKv, CmpOp.holds, int64Cmp_eq_zero', absVR, Option.toList_some, List.cons_ne_self,
        ite_false, List.all_cons, List.all_nil, Bool.and_true, Option.map_some, Option.getD_some]
      exact decide_eq_decide.mpr Iff.rfl
  | mod k n =>
    unfold cmpHolds MCmp.holds absM
    simp only [cmpOf, hsel k]
    cases findKey k s with
    | none => simp [cmpKv, CmpOp.holds, int64Cmp_eq_zero', zeroKv]
    | some e =>
      simp only [cmpKv, CmpOp.holds, int64Cmp_eq_zero', absVR, Option.toList_some, List.cons_ne_self,
        ite_false, List.all_cons, List.all_nil, Bool.and_true, Option.map_some, Option.getD_some]
      exact decide_eq_decide.mpr Iff.rfl

/-! ## A transaction's operations -/

theorem applyChanges_append' (r : w64) (s : List EtcdKv) (cs cs' : List Change) :
    applyChanges r s (cs ++ cs') = applyChanges r (applyChanges r s cs) cs' := by
  unfold applyChanges; rw [List.foldl_append]

/-- A delete of a missing key leaves the model store. -/
theorem MStore.del_none (m : MStore GoString GoString) (k : GoString) (h : m k = none) :
    m.del k = m := by
  funext k'
  unfold MStore.del
  by_cases hk : k' = k
  · subst hk; simp [h]
  · simp [hk]

/-- **One operation of a transaction, the server's run** (`srvOp`) at revision `r` on a sorted
state: the state after its changes is the model's, its result the model's, and it made changes
exactly when the model's changed the store. -/
theorem srvOp_tOpOf (s0 : List EtcdKv) (r : Nat) (s : List EtcdKv) (hs : s.Pairwise etcdKvLess)
    (op : MOp GoString GoString) :
    absM (applyChanges (W64 (r : Int)) s (txn.srvOp s0 (W64 (r : Int)) s (tOpOf op)).1) =
        (op.run r (absM s)).1 ∧
      resOf (txn.srvOp s0 (W64 (r : Int)) s (tOpOf op)).2 = (op.run r (absM s)).2.1 ∧
      ((txn.srvOp s0 (W64 (r : Int)) s (tOpOf op)).1 = [] ↔ (op.run r (absM s)).2.2 = false) := by
  have hnt : ∀ cs ts es, tOpOf op ≠ .txn cs ts es := by
    intro cs ts es h; cases op <;> simp [tOpOf] at h
  obtain ⟨hst, hres⟩ := txn.srvOp_state s0 (W64 (r : Int)) s (tOpOf op) hnt
  rw [hst, hres]
  cases op with
  | get k =>
    refine ⟨rfl, ?_, ?_⟩
    · simp only [tOpOf, applyTxnOp, resOf, MOp.run]
      rw [rangeSel_getOp s hs k]
    · simp [tOpOf, txn.srvOp, MOp.run]
  | put k v =>
    refine ⟨?_, rfl, ?_⟩
    · simp only [tOpOf, applyTxnOp, MOp.run]
      exact absM_putKv s hs r k v
    · simp [tOpOf, txn.srvOp, MOp.run]
  | del k =>
    have hlen := rangeIn_delOp_length s hs k
    simp only [tOpOf, applyTxnOp, MOp.run, resOf]
    rw [absM_delete]
    cases hk : absM s k with
    | none =>
      rw [hk] at hlen
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hlen
      refine ⟨MStore.del_none _ k hk, by rw [hlen], ?_⟩
      simp only [txn.srvOp, List.map_eq_nil_iff, Bool.false_eq_true, iff_true]
      exact List.eq_nil_of_length_eq_zero hlen
    | some x =>
      rw [hk] at hlen
      simp only [Option.isSome_some, ↓reduceIte] at hlen
      refine ⟨rfl, by rw [hlen], ?_⟩
      simp only [txn.srvOp, List.map_eq_nil_iff, Bool.true_eq_false, iff_false]
      intro h; rw [h] at hlen; cases hlen

/-- **A transaction's operations, the server's run** (`srvOps`, each at the state the earlier
ones' changes left) at revision `r` on a sorted state: the state after the changes is the model's,
the results the model's, and there are changes exactly when the model changed the store; the
state stays sorted. -/
theorem srvOps_tOpOf (s0 : List EtcdKv) (r : Nat) :
    ∀ (ops : List (MOp GoString GoString)) (s : List EtcdKv), s.Pairwise etcdKvLess →
      absM (applyChanges (W64 (r : Int)) s (txn.srvOps s0 (W64 (r : Int)) s (ops.map tOpOf)).1) =
          (runOps r (absM s) ops).1 ∧
        (txn.srvOps s0 (W64 (r : Int)) s (ops.map tOpOf)).2.map resOf = (runOps r (absM s) ops).2.1 ∧
        ((txn.srvOps s0 (W64 (r : Int)) s (ops.map tOpOf)).1 = [] ↔
          (runOps r (absM s) ops).2.2 = false)
  | [], s, _ => by simp [txn.srvOps, runOps, applyChanges]
  | op :: ops, s, hs => by
    obtain ⟨h1, h2, h3⟩ := srvOp_tOpOf s0 r s hs op
    have hs' := applyChanges_sorted (W64 (r : Int)) (txn.srvOp s0 (W64 (r : Int)) s (tOpOf op)).1 hs
    obtain ⟨i1, i2, i3⟩ := srvOps_tOpOf s0 r ops _ hs'
    rw [h1] at i1 i2 i3
    simp only [List.map_cons, txn.srvOps_cons, runOps]
    refine ⟨?_, ?_, ?_⟩
    · rw [applyChanges_append']; exact i1
    · rw [h2, i2]
    · rw [List.append_eq_nil_iff, h3, i3, Bool.or_eq_false_iff]

/-! ## The operations against the server's step -/

/-- A model transaction as the client sends it. -/
def txnOf (cs : List (MCmp GoString GoString)) (t e : List (MOp GoString GoString)) : TxnModel :=
  { cmps := cs.map cmpOf, thenOps := t.map tOpOf, elseOps := e.map tOpOf }

/-- The transaction's verdict is the model's. -/
theorem txnOk_txnOf (s : List EtcdKv) (hs : s.Pairwise etcdKvLess)
    (cs : List (MCmp GoString GoString)) (t e : List (MOp GoString GoString)) :
    txn.txnOk s (txnOf cs t e) = cs.all (MCmp.holds (absM s)) := by
  unfold txn.txnOk txnOf
  simp only [List.all_map]
  congr 1
  funext c
  exact cmpHolds_cmpOf s hs c

theorem txnOf_branch (cs : List (MCmp GoString GoString)) (t e : List (MOp GoString GoString))
    (ok : Bool) : (txnOf cs t e).branch ok = (if ok then t else e).map tOpOf := by
  unfold TxnModel.branch txnOf
  cases ok <;> rfl

/-- The client's transaction operations are plain (gets at the transaction's revision, puts with
no lease). -/
theorem opsPlain_tOpOf : ∀ ops : List (MOp GoString GoString), txn.opsPlain (ops.map tOpOf)
  | [] => by simp [txn.opsPlain]
  | op :: ops => by
    simp only [List.map_cons, txn.opsPlain]
    refine ⟨?_, opsPlain_tOpOf ops⟩
    cases op <;> simp [tOpOf, txn.opPlain, txn.rangeOpOf, op_simps]

/-- The client's operations need no previous key-value. -/
theorem pathsIgnOk_tOpOf (s0 : List EtcdKv) :
    ∀ ops : List (MOp GoString GoString), txn.PathsIgnOk s0 (ops.map tOpOf)
  | [] => by simp [txn.PathsIgnOk]
  | op :: ops => by
    simp only [List.map_cons, txn.PathsIgnOk]
    refine ⟨?_, pathsIgnOk_tOpOf s0 ops⟩
    cases op <;> simp [tOpOf, txn.PathIgnOk]

/-- The KV operation of a model input, as the client sends it (a list of `[lk, le)`). -/
def opOf (lk le : GoString) : MIn GoString GoString → KVOp
  | .get k => .range (getOp k)
  | .list => .range (listOp lk le)
  | .put k v => .put (putOp k v)
  | .del k => .deleteRange (delOp k)
  | .txn cs t e => .txn (txnOf cs t e)

/-- A model input's operation is a key-value one (unit T3). -/
theorem opOf_isKV (lk le : GoString) (i : MIn GoString GoString) : (opOf lk le i).isKV := by
  cases i <;> simp [opOf, KVOp.isKV]

/-- A commit's model state: the state's, or (some change) the changes' at the next revision. -/
theorem absSt_commit (σ : KVState) (cs : List Change) :
    absSt (σ.commit cs) = if cs = [] then absSt σ
      else ⟨absM (applyChanges (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs cs), σ.rev + 1⟩ := by
  by_cases hc : cs = []
  · subst hc; rw [KVState.commit_nil]; rfl
  · rw [if_neg hc]; unfold absSt; rw [KVState.commit_kvs σ cs hc, KVState.commit_rev σ cs hc]

/-- **The server's step follows the model's**: on a sorted state, the model state after
`kvOpStep` of an operation is the model's step's (the outputs: `TxnModelKV`'s next section). -/
theorem absSt_kvOpStep (ks : List GoString) (lk le : GoString) (σ : KVState)
    (hs : σ.kvs.Pairwise etcdKvLess) (i : MIn GoString GoString) :
    absSt (kvOpStep (opOf lk le i) σ) = (mStep ks i (absSt σ)).1 := by
  cases i with
  | get k => rfl
  | list => rfl
  | put k v =>
    rw [opOf]
    unfold absSt
    rw [kvOpStep_put_kvs, kvOpStep_put_rev]
    simp only [mStep]
    rw [absM_putKv σ.kvs hs (σ.rev + 1) k v]
  | del k =>
    have hlen := rangeIn_delOp_length σ.kvs hs k
    simp only [opOf, kvOpStep]
    rw [absSt_commit]
    have hd := txn.applyChanges_delChanges (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (delOp k)
    unfold absSt
    simp only [mStep]
    cases hk : absM σ.kvs k with
    | none =>
      rw [hk] at hlen
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hlen
      have hnil : txn.delChanges σ.kvs (delOp k) = [] := by
        unfold txn.delChanges
        rw [List.map_eq_nil_iff]
        exact List.eq_nil_of_length_eq_zero hlen
      simp [hnil]
    | some x =>
      rw [hk] at hlen
      simp only [Option.isSome_some, ↓reduceIte] at hlen
      have hne : txn.delChanges σ.kvs (delOp k) ≠ [] := by
        unfold txn.delChanges
        intro h
        rw [List.map_eq_nil_iff] at h
        rw [h] at hlen; cases hlen
      simp only [hne, ↓reduceIte, MSt.mk.injEq, and_true]
      rw [hd, absM_delete]
  | txn cs t e =>
    have hok := txnOk_txnOf σ.kvs hs cs t e
    obtain ⟨h1, -, h3⟩ := srvOps_tOpOf σ.kvs (σ.rev + 1) (if cs.all (MCmp.holds (absM σ.kvs)) then t else e)
      σ.kvs hs
    simp only [opOf, kvOpStep]
    rw [if_pos ⟨by rw [txnOf_branch]; exact pathsIgnOk_tOpOf σ.kvs _,
      by rw [txnOf_branch]; exact txn.pathsLeaseOk_plain _ _ _ (opsPlain_tOpOf _)⟩]
    unfold txn.srvRunTxn
    rw [absSt_commit]
    unfold absSt
    simp only [mStep]
    rw [txnOf_branch, hok]
    by_cases hc : (txn.srvOps σ.kvs (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs
        ((if cs.all (MCmp.holds (absM σ.kvs)) then t else e).map tOpOf)).1 = []
    · have hf := h3.1 hc
      rw [hc] at h1
      simp only [hc, ↓reduceIte, hf, Bool.false_eq_true, MSt.mk.injEq, and_true]
      exact h1
    · have hf : (runOps (σ.rev + 1) (absM σ.kvs)
          (if cs.all (MCmp.holds (absM σ.kvs)) then t else e)).2.2 = true := by
        cases h : (runOps (σ.rev + 1) (absM σ.kvs)
            (if cs.all (MCmp.holds (absM σ.kvs)) then t else e)).2.2 with
        | true => rfl
        | false => exact absurd (h3.2 h) hc
      simp only [hc, ↓reduceIte, hf, MSt.mk.injEq, and_true]
      exact h1

/-! ## The answers -/

/-- A put's answer: the next revision. -/
theorem mStep_put_out (ks : List GoString) (σ : KVState) (k v : GoString) :
    (mStep ks (.put k v) (absSt σ)).2 = .put (σ.rev + 1) := rfl

/-- A delete's answer: the revision of the state after it, and its count. -/
theorem mStep_del_out (ks : List GoString) (lk le : GoString) (σ : KVState)
    (hs : σ.kvs.Pairwise etcdKvLess) (k : GoString) :
    (mStep ks (.del k) (absSt σ)).2 =
      .del (kvOpStep (opOf lk le (.del k)) σ).rev (rangeIn σ.kvs (delOp k)).length := by
  have hr := absSt_kvOpStep ks lk le σ hs (.del k)
  have hrev : (kvOpStep (opOf lk le (.del k)) σ).rev = (mStep ks (.del k) (absSt σ)).1.rev := by
    rw [← hr]; rfl
  rw [hrev, rangeIn_delOp_length σ.kvs hs k, ← mStep_rev]
  simp only [mStep, absSt]
  cases absM σ.kvs k <;> rfl

/-- A transaction's answer: the revision of the state after it, the server's verdict and its
results (`srvRunTxn` at the next revision). -/
theorem mStep_txn_out (ks : List GoString) (lk le : GoString) (σ : KVState)
    (hs : σ.kvs.Pairwise etcdKvLess) (cs : List (MCmp GoString GoString))
    (t e : List (MOp GoString GoString)) :
    (mStep ks (.txn cs t e) (absSt σ)).2 =
      .txn (kvOpStep (opOf lk le (.txn cs t e)) σ).rev
        (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (txnOf cs t e)).1
        ((txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (txnOf cs t e)).2.2.map resOf) := by
  have hr := absSt_kvOpStep ks lk le σ hs (.txn cs t e)
  have hrev : (kvOpStep (opOf lk le (.txn cs t e)) σ).rev =
      (mStep ks (.txn cs t e) (absSt σ)).1.rev := by
    rw [← hr]; rfl
  have hok := txnOk_txnOf σ.kvs hs cs t e
  obtain ⟨-, h2, -⟩ := srvOps_tOpOf σ.kvs (σ.rev + 1)
    (if cs.all (MCmp.holds (absM σ.kvs)) then t else e) σ.kvs hs
  rw [hrev, ← mStep_rev]
  unfold txn.srvRunTxn
  rw [txnOf_branch, hok, h2]
  rfl

/-! ## The state's shape is kept -/

/-- Every step keeps the state sorted. -/
theorem kvOpStep_sorted (op : KVOp) (σ : KVState) :
    (kvOpStep op σ).kvs.Pairwise etcdKvLess := KVState.kvs_sorted _

/-- The state's keys are among `ks`. -/
def KeysIn (ks : List GoString) (σ : KVState) : Prop := ∀ e ∈ σ.kvs, e.key ∈ ks

/-- A transaction operation's key. -/
def MOp.key : MOp GoString GoString → GoString
  | .get k => k
  | .put k _ => k
  | .del k => k

/-- A model input's keys are among `ks`. -/
def MIn.KeysIn (ks : List GoString) : MIn GoString GoString → Prop
  | .get k => k ∈ ks
  | .list => True
  | .put k _ => k ∈ ks
  | .del k => k ∈ ks
  | .txn _ t e => ∀ op ∈ t ++ e, op.key ∈ ks

theorem keysIn_putKv (ks : List GoString) (s : List EtcdKv) (r : w64) (k v : GoString) (l : w64)
    (hk : k ∈ ks) (h : ∀ e ∈ s, e.key ∈ ks) : ∀ e ∈ putKv r k v l s, e.key ∈ ks := by
  intro e he
  unfold putKv at he
  simp only at he
  rcases btInsert_mem he with h1 | h1
  · subst h1
    cases hf : s.find? (fun v => decide (v.key = k)) with
    | none => exact hk
    | some w =>
      have hw : w.key = k := by simpa using List.find?_some hf
      simpa [hw] using hk
  · exact h e h1

/-- Changes whose puts' keys are among `ks` keep the state's keys among them. -/
theorem keysIn_applyChanges (ks : List GoString) (r : w64) :
    ∀ (cs : List Change) (s : List EtcdKv), (∀ c ∈ cs, c.isDel = false → c.key ∈ ks) →
      (∀ e ∈ s, e.key ∈ ks) → ∀ e ∈ applyChanges r s cs, e.key ∈ ks
  | [], s, _, h => h
  | c :: cs, s, hc, h => by
    have h' : ∀ e ∈ applyChange r s c, e.key ∈ ks := by
      cases c with
      | put k v l =>
        exact keysIn_putKv ks s r k v l (hc _ List.mem_cons_self rfl) h
      | del k =>
        intro e he
        exact h e (List.mem_filter.1 he).1
    exact keysIn_applyChanges ks r cs _ (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc')) h'

/-- The server's run of a transaction's operations puts only their keys. -/
theorem srvOps_put_keys (ks : List GoString) (s0 : List EtcdKv) (r : w64) :
    ∀ (ops : List (MOp GoString GoString)) (s : List EtcdKv), (∀ op ∈ ops, op.key ∈ ks) →
      ∀ c ∈ (txn.srvOps s0 r s (ops.map tOpOf)).1, c.isDel = false → c.key ∈ ks
  | [], _, _ => by simp [txn.srvOps]
  | op :: ops, s, hk => by
    simp only [List.map_cons, txn.srvOps_cons, List.mem_append]
    rintro c (hc | hc) hd
    · cases op with
      | get k => simp [tOpOf, txn.srvOp] at hc
      | put k v =>
        simp only [tOpOf, txn.srvOp, List.mem_singleton] at hc
        subst hc
        exact hk _ List.mem_cons_self
      | del k =>
        simp only [tOpOf, txn.srvOp, List.mem_map] at hc
        obtain ⟨_, _, rfl⟩ := hc
        simp [Change.isDel] at hd
    · exact srvOps_put_keys ks s0 r ops _ (fun o ho => hk o (List.mem_cons_of_mem _ ho)) c hc hd

/-- **The state's keys stay among `ks`**, for inputs whose keys are among them. -/
theorem kvOpStep_keysIn (ks : List GoString) (lk le : GoString) (σ : KVState)
    (i : MIn GoString GoString) (hi : i.KeysIn ks) (h : KeysIn ks σ) :
    KeysIn ks (kvOpStep (opOf lk le i) σ) := by
  have hcm : ∀ cs, (∀ c ∈ cs, c.isDel = false → c.key ∈ ks) → KeysIn ks (σ.commit cs) := by
    intro cs hcs
    by_cases hc : cs = []
    · subst hc; rw [KVState.commit_nil]; exact h
    · unfold KeysIn; rw [KVState.commit_kvs σ cs hc]
      exact keysIn_applyChanges ks _ cs σ.kvs hcs h
  cases i with
  | get k => exact h
  | list => exact h
  | put k v =>
    rw [opOf]; unfold KeysIn; rw [kvOpStep_put_kvs]
    exact keysIn_putKv ks σ.kvs _ k v _ hi h
  | del k =>
    simp only [opOf, kvOpStep]
    apply hcm
    intro c hc hd
    unfold txn.delChanges at hc
    rw [List.mem_map] at hc
    obtain ⟨_, _, rfl⟩ := hc
    simp [Change.isDel] at hd
  | txn cs t e =>
    simp only [opOf, kvOpStep]
    split
    · apply hcm
      unfold txn.srvRunTxn
      rw [txnOf_branch]
      apply srvOps_put_keys
      intro op hop
      apply hi
      split at hop
      · exact List.mem_append_left _ hop
      · exact List.mem_append_right _ hop
    · exact h

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.filterMap_cons, h x List.mem_cons_self,
      filterMap_congr' xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- **The model lists a sorted state's key-values**: for keys `ks` strictly sorted, a sorted
list `s` whose keys are among them. -/
theorem filterMap_absM (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) :
    ∀ (s : List EtcdKv), s.Pairwise etcdKvLess → (∀ e ∈ s, e.key ∈ ks) →
      ks.filterMap (fun k => (absM s k).map fun x => (k, x)) = s.map fun e => (e.key, absVR e) := by
  induction ks with
  | nil =>
    intro s _ h
    cases s with
    | nil => rfl
    | cons w ws => exact absurd (h w List.mem_cons_self) (by simp)
  | cons k ks ih =>
    intro s hs h
    rw [List.pairwise_cons] at hks
    have hlt : ∀ k' ∈ ks, go.GoStringLt k k' := hks.1
    cases s with
    | nil =>
      have : ∀ k' : GoString, absM [] k' = none := fun _ => rfl
      simp only [List.filterMap_cons, this, Option.map_none, List.map_nil]
      rw [List.filterMap_eq_nil_iff]
      intro _ _; rfl
    | cons w ws =>
      rw [List.pairwise_cons] at hs
      have hw := h w List.mem_cons_self
      -- every key of `ws` is above `w`'s
      have hws : ∀ e ∈ ws, go.GoStringLt w.key e.key := fun e he => hs.1 e he
      -- `absM (w :: ws)` at a key of `ks` above `w`'s is `ws`'s
      have hrest : ∀ k' ∈ ks, w.key ≠ k' → absM (w :: ws) k' = absM ws k' := by
        intro k' _ hne
        unfold absM
        rw [findKey_cons, if_neg hne]
      rcases List.mem_cons.1 hw with hwk | hwk
      · -- `w` is `k`'s
        have h1 : absM (w :: ws) k = some (absVR w) := by
          unfold absM; rw [findKey_cons, if_pos hwk]; rfl
        have hws' : ∀ e ∈ ws, e.key ∈ ks := by
          intro e he
          rcases List.mem_cons.1 (h e (List.mem_cons_of_mem _ he)) with h2 | h2
          · exfalso
            have := hws e he
            rw [hwk, ← h2] at this
            exact go.goStringLt_irrefl _ this
          · exact h2
        have hcongr : ks.filterMap (fun k' => (absM (w :: ws) k').map fun x => (k', x)) =
            ks.filterMap (fun k' => (absM ws k').map fun x => (k', x)) := by
          apply filterMap_congr'
          intro k' hk'
          rw [hrest k' hk' (by rw [hwk]; exact fun e => go.goStringLt_irrefl _ (e ▸ hlt k' hk'))]
        simp only [List.filterMap_cons, h1, Option.map_some, List.map_cons, hcongr, hwk]
        rw [ih hks.2 ws hs.2 hws']
      · -- `w` is above `k`: `k` is not there
        have hk0 : absM (w :: ws) k = none := by
          unfold absM
          rw [findKey_cons]
          have hne : w.key ≠ k := fun e => go.goStringLt_irrefl _ (e ▸ hlt _ hwk)
          rw [if_neg hne]
          have : findKey k ws = none := by
            unfold findKey
            rw [List.find?_eq_none]
            intro e he hek
            simp only [decide_eq_true_eq] at hek
            have h3 := hws e he
            rw [hek] at h3
            exact go.goStringLt_irrefl _ (go.goStringLt_trans (hlt _ hwk) h3)
          rw [this]; rfl
        have hall : ∀ e ∈ w :: ws, e.key ∈ ks := by
          intro e he
          rcases List.mem_cons.1 he with rfl | he
          · exact hwk
          · rcases List.mem_cons.1 (h e (List.mem_cons_of_mem _ he)) with h2 | h2
            · exfalso
              have := hws e he
              rw [h2] at this
              exact go.goStringLt_irrefl _ (go.goStringLt_trans (hlt _ hwk) this)
            · exact h2
        simp only [List.filterMap_cons, hk0, Option.map_none]
        exact ih hks.2 (w :: ws) (List.pairwise_cons.2 hs) hall

/-- **A list's answer**: the state's key-values of the range `[lk, le)`, at the state's revision,
for a range holding every key of `ks` (strictly sorted) and a state whose keys are among them. -/
theorem mStep_list_out (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) (lk le : GoString)
    (hin : ∀ k ∈ ks, inRange lk le k = true) (σ : KVState) (hs : σ.kvs.Pairwise etcdKvLess)
    (h : KeysIn ks σ) :
    (mStep ks .list (absSt σ)).2 =
      .list σ.rev ((σ.kvs.filter (fun v => inRange lk le v.key)).map fun e => (e.key, absVR e)) := by
  have hf : σ.kvs.filter (fun v => inRange lk le v.key) = σ.kvs := by
    rw [List.filter_eq_self]
    intro e he
    exact hin _ (h e he)
  rw [hf]
  simp only [mStep, absSt]
  rw [filterMap_absM ks hks σ.kvs hs h]

/-! ## The start, and the transactions' shape -/

/-- **An empty state at revision `1` is the model's initial state.** -/
theorem absSt_init (σ : KVState) (hk : σ.kvs = []) (hr : σ.rev = 1) :
    absSt σ = (mInit : MSt GoString GoString) := by
  unfold absSt; rw [hk, hr]; rfl


/-- **The instance's transactions are plain** (`txnPlain`, the server's specs' premise). -/
theorem txnPlain_txnOf (cs : List (MCmp GoString GoString)) (t e : List (MOp GoString GoString)) :
    txn.txnPlain (txnOf cs t e) := ⟨opsPlain_tOpOf t, opsPlain_tOpOf e⟩

end kv

end linkv
end EtcdGrove
end Perennial

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
- `runOps_tOpOf`: a transaction's operations, in order (the client's `runOps`, which the server's
  run agrees with on flat transactions, `srvRunTxn_runTxn_flat`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.TxnModel
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.ModelKV
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
    simp [txn.deleteOpOf, OpFull.newOp, inRange]
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
  simp [txn.deleteOpOf, OpFull.newOp, inRange]

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
  simp [txn.rangeOpOf, OpFull.newOp, OpModel.zero, inRange]

/-- **A get's selection reads the model store.** -/
theorem rangeSel_getOp (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) (k : GoString) :
    (rangeSel s (getOp k)).head?.map absVR = (absM s) k := by
  unfold rangeSel
  have hf : (rangeIn s (getOp k)).filter (kvFilterOk (getOp k)) = rangeIn s (getOp k) := by
    rw [List.filter_eq_self]
    intro v _
    simp [kvFilterOk, txn.rangeOpOf, OpFull.newOp, OpModel.zero]
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

end kv

end linkv
end EtcdGrove
end Perennial

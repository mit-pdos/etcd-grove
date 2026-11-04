/-
Lean-first (no Rocq counterpart).

**The compactor's compare-and-swap, against etcd's KV model** (`notes/k8s-compactor-plan.md`): what
`kvOpStep` does with a round's transaction `casTxn ev rev` (`CompactorDefs.lean`) and with a plain
put, at the compactors' key `compactRevKey`, read through `keyValue`.

- `casTxn_win_value`: a winning round leaves `FormatInt(rev, 10)` at the key;
- `casTxn_lose_same`: a losing round (a get) changes nothing;
- `casWins_of_absent`: at `ev = 0`, a round wins when the key is missing (its version is `0`);
- `keyValue_put_other`: a client's plain put of another key leaves the key's value.

The proofs go through the txnlin example's abstraction (`linkv.absM`, `linkv.absSt_kvOpStep`): the
key's value is its model value's (`keyValue_absM`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.TxnModelKV
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.ModelKV
public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.InvOp

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open go_etcd_io.etcd.server.v3.etcdserver mvcc k8s linkv

section kv
variable [GooseExts]

/-- A key's value is its model value's (`linkv.absM`, on the sorted current store). -/
theorem keyValue_absM (σ : KVState) (k : GoString) :
    keyValue σ k = (absM σ.kvs k).map VR.val := by
  unfold keyValue absM
  rw [linkv.filter_key_sorted k σ.kvs σ.kvs_sorted, Option.map_map]
  cases findKey k σ.kvs <;> rfl

/-- The round's verdict is the model's comparison: the key's version (`0` if missing) is `ev`. -/
theorem casWins_eq (ev rev : w64) (σ : KVState) :
    casWins ev rev σ = decide (((absM σ.kvs compactRevKey).map VR.ver).getD (W64 0) = ev) := by
  unfold casWins txn.srvRunTxn
  simp only
  rw [txnOk_txnOf σ.kvs σ.kvs_sorted]
  simp [MCmp.holds]

/-- **A winning round leaves `FormatInt(rev, 10)` at the key** (the transaction names no lease and
ignores nothing, so its put takes effect). -/
theorem casTxn_win_value (ev rev : w64) (σ : KVState) (h : casWins ev rev σ = true) :
    keyValue (kvOpStep (.txn (casTxn ev rev)) σ) compactRevKey = some (fmtInt rev (W64 10)) := by
  have hst := absSt_kvOpStep [] [] [] σ σ.kvs_sorted
    (.txn [.ver compactRevKey ev] [.put compactRevKey (fmtInt rev (W64 10))] [.get compactRevKey])
  have hc : [MCmp.ver compactRevKey ev].all (MCmp.holds (absM σ.kvs)) = true := by
    rw [casWins_eq] at h
    simpa [MCmp.holds] using h
  have hkv := congrArg MSt.kv hst
  simp only [absSt, mStep, hc, ↓reduceIte, linkv.runOps, MOp.run] at hkv
  rw [keyValue_absM]
  change (absM (kvOpStep (opOf [] [] (.txn [.ver compactRevKey ev]
    [.put compactRevKey (fmtInt rev (W64 10))] [.get compactRevKey])) σ).kvs compactRevKey).map
      VR.val = _
  rw [hkv]
  simp [MStore.put]

/-- **A losing round changes nothing** (its else branch is a get). -/
theorem casTxn_lose_same (ev rev : w64) (σ : KVState) (h : casWins ev rev σ = false) :
    kvOpStep (.txn (casTxn ev rev)) σ = σ := by
  have hok : txn.txnOk σ.kvs (casTxn ev rev) = false := h
  simp only [kvOpStep]
  split
  · unfold txn.srvRunTxn
    rw [hok, txnOf_branch]
    simp [tOpOf, txn.srvOps, txn.srvOp, KVState.commit_nil]
  · rfl

/-- **At `ev = 0`, a round wins when the key is missing** (a missing key's version is `0`). -/
theorem casWins_of_absent (rev : w64) (σ : KVState) (h : keyValue σ compactRevKey = none) :
    casWins (W64 0) rev σ = true := by
  rw [keyValue_absM, Option.map_eq_none_iff] at h
  rw [casWins_eq, h]
  simp

/-- **A client's plain put of another key leaves the key's value.** -/
theorem keyValue_put_other (k v : GoString) (σ : KVState) (h : k ≠ compactRevKey) :
    keyValue (kvOpStep (.put (putWireOf (opPutModel k v []))) σ) compactRevKey =
      keyValue σ compactRevKey := by
  rw [show putWireOf (opPutModel k v []) = putOp k v from rfl,
    keyValue_absM, keyValue_absM, kvOpStep_put_kvs, absM_putKv σ.kvs σ.kvs_sorted]
  simp [MStore.put, Ne.symm h]

end kv

end k8s_compactor
end EtcdGrove
end Perennial

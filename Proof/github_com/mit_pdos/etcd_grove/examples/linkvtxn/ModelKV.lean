/-
Lean-first (no Rocq counterpart).

# linkv: the client's plain put and get as etcd's operations (2026-10-19)

The put and the get the client sends for `cli.Put(ctx, k, v)` and `cli.Get(ctx, k)` (`putOp k v`,
`getOp k`: `client/v3/Results.lean`'s `putKeyOp`, `getKeyOp`) and what the server's step does with
them on a state sorted by key: a put commits its one change at the next revision
(`kvOpStep_put_kvs`, `kvOpStep_put_rev`, finding the value it wrote, `findKey_putKv_val`); a get changes nothing (`kvOpStep_get`). `TxnModelKV.lean` builds on them.

Moved from `examples/linkv/ModelKV.lean` when linkv was retired (2026-10-22, `notes/decisions.md`
D34), without linkv's values-only porcupine model (`KVModel.lean`) and its abstraction `absKV`; the
names keep their namespace `linkv`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LogLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

section kv
variable [ext : FfiSyntax]

/-- The put of `k ↦ v` with no options (`client/v3/Results.lean`'s `putKeyOp`: what
`cli.Put(ctx, k, v)` sends). -/
abbrev putOp (k v : GoString) : OpFull := txn.putOpOf k v (W64 0) false false false

/-- The get of `k` with no options (`client/v3/Results.lean`'s `getKeyOp`: what
`cli.Get(ctx, k)` sends). -/
abbrev getOp (k : GoString) : OpFull :=
  txn.rangeOpOf k [] (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0) (W64 0) (W64 0)
    (W64 0)

/-- The put of `k ↦ v` finds the value it wrote (`client/v3/Results.lean`'s
`findKey_putKv_value`, restated to keep the client's proof out of the imports). -/
theorem findKey_putKv_val (s : List EtcdKv) (hs : s.Pairwise etcdKvLess) (r : w64)
    (k v : GoString) (l : w64) :
    ∃ nv, mvcc.findKey k (putKv r k v l s) = some nv ∧ nv.key = k ∧ nv.value = v := by
  unfold putKv
  simp only
  rw [mvcc.findKey_btInsert _ s hs]
  cases h : s.find? (fun v => decide (v.key = k)) with
  | none =>
    refine ⟨{ key := k, createRev := r, modRev := r, version := W64 1, value := v, lease := l },
      ?_, rfl, rfl⟩
    simp
  | some kv =>
    have hk : kv.key = k := by simpa using List.find?_some h
    refine ⟨{ kv with modRev := r, version := kv.version + W64 1, value := v, lease := l }, ?_,
      hk, rfl⟩
    simp [hk]

/-- What `kvOpStep` does with a plain put: commit its one change at the next revision. -/
theorem kvOpStep_put_kvs (k v : GoString) (σ : KVState) :
    (kvOpStep (.put (putOp k v)) σ).kvs = putKv (W64 ((σ.rev + 1 : Nat) : Int)) k v (W64 0) σ.kvs := by
  simp [kvOpStep, KVState.commit_kvs, KVState.leaseMissing, txn.needsPrev, txn.putOpOf, op_simps, txn.putChangeOf,
    txn.putValOf, txn.putLeaseOf, mvcc.applyChanges, mvcc.applyChange]

theorem kvOpStep_put_rev (k v : GoString) (σ : KVState) :
    (kvOpStep (.put (putOp k v)) σ).rev = σ.rev + 1 := by
  simp [kvOpStep, KVState.commit_rev, KVState.leaseMissing, txn.needsPrev, txn.putOpOf, op_simps]

/-- **A get changes nothing.** -/
theorem kvOpStep_get (k : GoString) (σ : KVState) : kvOpStep (.range (getOp k)) σ = σ := rfl

end kv

end linkv
end EtcdGrove
end Perennial

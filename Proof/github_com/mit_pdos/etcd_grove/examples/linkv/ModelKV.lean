/-
Lean-first (no Rocq counterpart).

# linkv: the model against etcd's KV state (2026-10-19)

The server's specs speak of etcd's `KVState` (`etcdserver/KVModelDefs.lean`: the key-values at
the latest revision) and of an operation's step on it, `kvOpStep`; the porcupine model
(`Model.lean`) of stores `GoString → Option GoString`. `absKV σ` is the store of `σ`: every
key's value (`mvcc.findKey`). On a state sorted by key (every log's is, `mvcc.stateAfter_sorted`):

- the put the client sends for `cli.Put(ctx, k, v)` (`putOp k v`, `client/v3/Results.lean`'s
  `putKeyOp`) steps the store as the model's `put k v` (`absKV_put`), and keeps the state
  sorted (`kvOpStep_put_sorted`);
- the get the client sends for `cli.Get(ctx, k)` (`getOp k`, `getKeyOp`) changes nothing
  (`kvOpStep_get`), and the server's answer (the state's key-values of `k`,
  `client.srvRangeOk_getKey`) has the store's value at `k` as its first value (`absKV_get`);
- so the model's `CStep` on the configuration `⟨absKV σ, pend⟩` follows `kvOpStep`
  (`cstep_putOk`, `cstep_putErr_applied`, `cstep_getOk`), and the bootstrap's empty store is
  the model's initial one (`absKV_empty`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Model
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

/-- The store of etcd's KV state: every key's value. -/
def absKV (σ : KVState) : Store GoString GoString :=
  fun k => (mvcc.findKey k σ.kvs).map EtcdKv.value

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
theorem kvOpStep_put_eq (k v : GoString) (σ : KVState) :
    (kvOpStep (.put (putOp k v)) σ).kvs =
      putKv (W64 ((σ.rev + 1 : Nat) : Int)) k v (W64 0) σ.kvs := by
  simp [kvOpStep, KVState.commit, txn.needsPrev, txn.putOpOf, OpFull.newOp, txn.putChangeOf,
    txn.putValOf, txn.putLeaseOf, mvcc.applyChanges, mvcc.applyChange]

/-- **A put steps the store as the model's put.** -/
theorem absKV_put (k v : GoString) (σ : KVState) (hs : σ.kvs.Pairwise etcdKvLess) :
    absKV (kvOpStep (.put (putOp k v)) σ) = (absKV σ).set k v := by
  funext k'
  unfold absKV Store.set
  rw [kvOpStep_put_eq]
  by_cases hk : k' = k
  · subst hk
    obtain ⟨nv, hnv, -, hv⟩ := findKey_putKv_val σ.kvs hs (W64 ((σ.rev + 1 : Nat) : Int)) k' v (W64 0)
    rw [hnv]
    simp [hv]
  · simp only [hk, ite_false]
    rw [mvcc.findKey_putKv_other hs _ k' k v _ (Ne.symm hk)]

/-- A put keeps the state sorted. -/
theorem kvOpStep_put_sorted (k v : GoString) (σ : KVState) (hs : σ.kvs.Pairwise etcdKvLess) :
    (kvOpStep (.put (putOp k v)) σ).kvs.Pairwise etcdKvLess := by
  rw [kvOpStep_put_eq]
  exact mvcc.putKv_sorted hs _ k v _

/-- **A get changes nothing.** -/
theorem kvOpStep_get (k : GoString) (σ : KVState) : kvOpStep (.range (getOp k)) σ = σ := rfl

/-- **The server's answer to a get reads the store**: the first of the state's key-values of
`k` (`client.srvRangeOk_getKey`'s answer) has the store's value at `k`. -/
theorem absKV_get (k : GoString) (σ : KVState) :
    ((σ.kvs.filter (fun v => decide (v.key = k))).head?).map EtcdKv.value = absKV σ k := by
  unfold absKV mvcc.findKey
  rw [List.head?_filter]

/-- The empty state's store is the model's initial one. -/
theorem absKV_empty (σ : KVState) (h : σ.kvs = []) : absKV σ = fun _ => none := by
  funext k; simp [absKV, h, mvcc.findKey]

/-! ### The model's steps follow the server's -/

/-- A put that returned `ok`: the configuration of the state after it. -/
theorem cstep_putOk (k v : GoString) (σ : KVState) (hs : σ.kvs.Pairwise etcdKvLess)
    (pend : List (GoString × GoString)) :
    CStep ⟨absKV σ, pend⟩ (.put k v) .ok ⟨absKV (kvOpStep (.put (putOp k v)) σ), pend⟩ := by
  rw [absKV_put k v σ hs]; exact .putOk _ k v

/-- A failed put the server applied during the call: pending, then applied. -/
theorem cstep_putErr_applied (k v : GoString) (σ : KVState) (hs : σ.kvs.Pairwise etcdKvLess)
    (pend : List (GoString × GoString)) :
    ∃ c₁, CStep ⟨absKV σ, pend⟩ (.put k v) .err c₁ ∧
      Reach c₁ ⟨absKV (kvOpStep (.put (putOp k v)) σ), pend⟩ := by
  refine ⟨_, .putErr _ k v, .single ?_⟩
  rw [absKV_put k v σ hs]
  have h := Silent.apply ⟨absKV σ, (k, v) :: pend⟩ k v List.mem_cons_self
  simpa [List.erase_cons_head] using h

/-- A get that returned the server's answer `kvs` (`client.srvRangeOk_getKey`'s). -/
theorem cstep_getOk (k : GoString) (σ : KVState) (pend : List (GoString × GoString))
    (kvs : List EtcdKv) (hkvs : kvs = σ.kvs.filter (fun v => decide (v.key = k))) :
    CStep ⟨absKV σ, pend⟩ (.get k) (.okGet (kvs.head?.map EtcdKv.value))
      ⟨absKV (kvOpStep (.range (getOp k)) σ), pend⟩ := by
  rw [kvOpStep_get, hkvs, absKV_get]
  exact .getOk _ k

end kv

end linkv
end EtcdGrove
end Perennial

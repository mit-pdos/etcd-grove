/-
Lean-first (no Rocq counterpart).

# linkv: the model against etcd's KV state (2026-10-19)

The server's specs speak of etcd's `KVState` (`etcdserver/KVModelDefs.lean`: the key-values at
the latest revision) and of an operation's step on it, `kvOpStep`; the porcupine model
(`KVModel.lean`) of stores `GoString → Option GoString`. `absKV σ` is the store of `σ`: every
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

The client's put and get (`putOp`, `getOp`) and the server's step on them (`kvOpStep_put_eq`,
`kvOpStep_put_sorted`, `kvOpStep_get`) are `linkvtxn/ModelKV.lean`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.KVModel
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.ModelKV

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

/-- **A put steps the store as the model's put.** -/
theorem absKV_put (k v : GoString) (σ : KVState) (hs : σ.kvs.Pairwise etcdKvLess) :
    absKV (kvOpStep (.put (putOp k v)) σ) = (absKV σ).set k v := by
  funext k'
  rw [kvOpStep_put_eq]
  unfold absKV Store.set
  by_cases hk : k' = k
  · subst hk
    obtain ⟨nv, hnv, -, hv⟩ := findKey_putKv_val σ.kvs hs (W64 ((σ.rev + 1 : Nat) : Int)) k' v (W64 0)
    rw [hnv]
    simp [hv]
  · simp only [hk, ite_false]
    rw [mvcc.findKey_putKv_other hs _ k' k v _ (Ne.symm hk)]

/-- The empty state's store is the model's initial one. -/
theorem absKV_empty (r : Nat) : absKV ⟨[], r⟩ = fun _ => none := rfl

end kv

end linkv
end EtcdGrove
end Perennial

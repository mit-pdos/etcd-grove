/-
**authlease's cell, purely** (auth-lease S4, item 9): the steps of the operations the driver hands the
server, on the client's KV state (`kvOpStep`): a put of a key with a lease (`grantPut`'s), u's
transaction putting `a/txn` with its lease, a grant, a revocation; the leases they leave on the keys
(`leaseOf`) and the revisions they keep (`kvOpStep_at`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.EtcdModelKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.WinLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_authlease

open go_etcd_io.etcd.server.v3.etcdserver client

section pure
variable [GooseExts]

/-- The keys: `z/lease` (root's), `a/lease`, `a/txn` (u's), `a/x` (u's refused puts). -/
abbrev zK : GoString := go!"z/lease"
abbrev aK : GoString := go!"a/lease"
abbrev tK : GoString := go!"a/txn"
abbrev xK : GoString := go!"a/x"

/-- **The lease of the key `k`** in the key-values `s` (`none`: no key). -/
def leaseOf (k : GoString) (s : List EtcdKv) : Option w64 := (mvcc.findKey k s).map EtcdKv.lease

/-- **`grantPut`'s put**: `Put(k, "v", WithLease(L))`, as the server sees it. -/
abbrev leasePutOp (k : GoString) (L : w64) : OpFull := txn.putOpOf k go!"v" L false false false

theorem leasePut_wire (k : GoString) (L : w64) :
    putWireOf (opPutModel k go!"v" [withLeaseM L]) = leasePutOp k L := by
  simp [putWireOf, opPutModel, opFold, withLeaseM, OpFull.putInit, OpFull.newOp, OpModel.zero]

/-- **u's transaction**: `Txn().Then(OpPut(k, "v", WithLease(L)))`, as the client models it. -/
abbrev leaseTxn (k : GoString) (L : w64) : TxnModel :=
  { cmps := [], thenOps := [.put k go!"v" L], elseOps := [] }

theorem leaseOf_putKv_self {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (r : w64) (k v : GoString)
    (l : w64) : leaseOf k (putKv r k v l s) = some l := by
  unfold leaseOf
  rw [mvcc.findKey_putKv_self_eq hs]
  cases mvcc.findKey k s <;> rfl

theorem findKey_putKv_ne {s : List EtcdKv} (hs : s.Pairwise etcdKvLess) (r : w64) (k k' v : GoString)
    (l : w64) (hne : k' ≠ k) : mvcc.findKey k (putKv r k' v l s) = mvcc.findKey k s :=
  mvcc.findKey_putKv_other hs r k k' v l hne

/-- **A step keeps every revision up to the state's.** -/
theorem kvOpStep_at (op : KVOp) (σ : KVState) (r : Nat) (hr : r ≤ σ.rev) :
    (kvOpStep op σ).at r = σ.at r := by
  cases op with
  | put o =>
    simp only [kvOpStep]
    split
    · rfl
    split
    · rfl
    · exact KVState.commit_at σ _ r hr
  | range o => rfl
  | deleteRange o => exact KVState.commit_at σ _ r hr
  | txn t =>
    simp only [kvOpStep]
    split
    · exact KVState.commit_at σ _ r hr
    · rfl
  | leaseGrant id ttl =>
    simp only [kvOpStep]
    split <;> rfl
  | leaseRevoke id =>
    simp only [kvOpStep]
    split
    · exact KVState.commit_at σ _ r hr
    · rfl

theorem kvOpStep_rev_le (op : KVOp) (σ : KVState) : σ.rev ≤ (kvOpStep op σ).rev := by
  obtain ⟨cs, -, h⟩ := kvOpStep_commit op σ
  by_cases hc : cs = []
  · subst hc; rw [KVState.commit_nil] at h; omega
  · rw [KVState.commit_rev σ cs hc] at h; omega

/-- **`grantPut`'s put at a live lease**: the key's lease is `L`, the other keys kept, the table kept. -/
theorem step_leasePut_live (k : GoString) (L : w64) (σ : KVState) (hl : ¬ σ.leaseMissing L) :
    leaseOf k (kvOpStep (.put (leasePutOp k L)) σ).kvs = some L ∧
      (∀ k', k' ≠ k → mvcc.findKey k' (kvOpStep (.put (leasePutOp k L)) σ).kvs = mvcc.findKey k' σ.kvs) ∧
      (kvOpStep (.put (leasePutOp k L)) σ).leases = σ.leases := by
  have hk : (kvOpStep (.put (leasePutOp k L)) σ).kvs =
      putKv (W64 ((σ.rev + 1 : Nat) : Int)) k go!"v" L σ.kvs := by
    simp [kvOpStep, hl, KVState.commit_kvs, txn.needsPrev, mvcc.applyChanges, mvcc.applyChange,
      txn.putChangeOf, txn.putValOf, txn.putLeaseOf, txn.putOpOf]
  refine ⟨?_, fun k' hne => ?_, ?_⟩
  · rw [hk]; exact leaseOf_putKv_self σ.kvs_sorted _ _ _ _
  · rw [hk]; exact findKey_putKv_ne σ.kvs_sorted _ _ _ _ _ (Ne.symm hne)
  · simp [kvOpStep, hl, KVState.commit]; split <;> rfl

/-- **`grantPut`'s put at a missing lease** changes nothing. -/
theorem step_leasePut_missing (k : GoString) (L : w64) (σ : KVState) (hl : σ.leaseMissing L) :
    kvOpStep (.put (leasePutOp k L)) σ = σ := by
  simp [kvOpStep, hl]

/-- **u's transaction at a live lease** (`L ≠ 0`): `put`'s effect. -/
theorem step_leaseTxn_live (k : GoString) (L : w64) (σ : KVState) (hl : L ∈ σ.leases.ids) :
    leaseOf k (kvOpStep (.txn (txnWireOf (leaseTxn k L))) σ).kvs = some L ∧
      (∀ k', k' ≠ k → mvcc.findKey k' (kvOpStep (.txn (txnWireOf (leaseTxn k L))) σ).kvs =
        mvcc.findKey k' σ.kvs) ∧
      (kvOpStep (.txn (txnWireOf (leaseTxn k L))) σ).leases = σ.leases := by
  have hc : (txn.srvRunTxn (W64 ((σ.rev + 1 : Nat) : Int)) σ.kvs (txnWireOf (leaseTxn k L))).2.1 =
      [.put k go!"v" L] := by
    simp [txn.srvRunTxn, txnWireOf, opWire, TxnModel.branch, txn.srvOps_cons, txn.srvOps_nil, txn.srvOp]
  have hok : txn.PathsIgnOk σ.kvs ((txnWireOf (leaseTxn k L)).branch (txn.txnOk σ.kvs (txnWireOf (leaseTxn k L)))) ∧
      txn.PathsLeaseOk σ.kvs σ.leases.ids
        ((txnWireOf (leaseTxn k L)).branch (txn.txnOk σ.kvs (txnWireOf (leaseTxn k L)))) := by
    simp [txnWireOf, opWire, TxnModel.branch, txn.txnOk, txn.PathsIgnOk, txn.PathIgnOk,
      txn.PathsLeaseOk, txn.PathLeaseOk, hl]
  have hk : (kvOpStep (.txn (txnWireOf (leaseTxn k L))) σ).kvs =
      putKv (W64 ((σ.rev + 1 : Nat) : Int)) k go!"v" L σ.kvs := by
    simp only [kvOpStep, hok, and_self, ↓reduceIte, hc]
    rw [KVState.commit_kvs σ _ (by simp)]
    simp [mvcc.applyChanges, mvcc.applyChange]
  refine ⟨?_, fun k' hne => ?_, ?_⟩
  · rw [hk]; exact leaseOf_putKv_self σ.kvs_sorted _ _ _ _
  · rw [hk]; exact findKey_putKv_ne σ.kvs_sorted _ _ _ _ _ (Ne.symm hne)
  · simp only [kvOpStep, hok, and_self, ↓reduceIte, hc, KVState.commit]; split <;> rfl

/-- **u's transaction at a lease not in the table** changes nothing. -/
theorem step_leaseTxn_missing (k : GoString) (L : w64) (σ : KVState) (hl : L ≠ W64 0)
    (hn : L ∉ σ.leases.ids) : kvOpStep (.txn (txnWireOf (leaseTxn k L))) σ = σ := by
  have hno : ¬ (txn.PathsIgnOk σ.kvs ((txnWireOf (leaseTxn k L)).branch (txn.txnOk σ.kvs (txnWireOf (leaseTxn k L)))) ∧
      txn.PathsLeaseOk σ.kvs σ.leases.ids
        ((txnWireOf (leaseTxn k L)).branch (txn.txnOk σ.kvs (txnWireOf (leaseTxn k L))))) := by
    simp [txnWireOf, opWire, TxnModel.branch, txn.txnOk, txn.PathsLeaseOk, txn.PathLeaseOk, hn]
    intro _; exact hl
  simp only [kvOpStep, hno, ↓reduceIte]

/-- **A grant** keeps the key-values; the table gains `id` if it succeeds, and keeps its ids. -/
theorem step_grant (id ttl : w64) (σ : KVState) :
    (kvOpStep (.leaseGrant id ttl) σ).kvs = σ.kvs ∧
      (∀ i, i ∈ (kvOpStep (.leaseGrant id ttl) σ).leases.ids ↔ i ∈ σ.leases.ids ∨
        (leaseGrantOk σ.leases id ttl ∧ i = id)) := by
  simp only [kvOpStep]
  split
  · rename_i hg
    refine ⟨rfl, fun i => ?_⟩
    simp [LeaseTable.ids, hg]
  · rename_i hg
    exact ⟨rfl, fun i => by simp [hg]⟩

/-- **A revocation of a live lease** deletes exactly its keys and removes it from the table. -/
theorem step_revoke_live (id : w64) (σ : KVState) (hin : id ∈ σ.leases.ids) :
    (∀ k, leaseOf k σ.kvs = some id → mvcc.findKey k (kvOpStep (.leaseRevoke id) σ).kvs = none) ∧
      (∀ k l, leaseOf k σ.kvs = some l → l ≠ id →
        mvcc.findKey k (kvOpStep (.leaseRevoke id) σ).kvs = mvcc.findKey k σ.kvs) ∧
      (∀ k, mvcc.findKey k σ.kvs = none → mvcc.findKey k (kvOpStep (.leaseRevoke id) σ).kvs = none) ∧
      (∀ i, i ∈ (kvOpStep (.leaseRevoke id) σ).leases.ids ↔ i ∈ σ.leases.ids ∧ i ≠ id) := by
  let ks := (σ.kvs.filter (fun v => v.lease = id)).map EtcdKv.key
  have hrc : revokeChanges σ.kvs id = ks.map mvcc.Change.del := by
    unfold revokeChanges; simp [ks, List.map_map]
  have hk : (kvOpStep (.leaseRevoke id) σ).kvs = σ.kvs.filter (fun v => !decide (v.key ∈ ks)) := by
    simp only [kvOpStep, hin, ↓reduceIte]
    by_cases h0 : revokeChanges σ.kvs id = []
    · have hks : ks = [] := by rw [hrc] at h0; simpa using h0
      show (σ.commit _).kvs = _
      rw [h0, KVState.commit_nil, hks]
      exact (List.filter_eq_self.2 (fun _ _ => by simp)).symm
    · show (σ.commit _).kvs = _
      rw [KVState.commit_kvs σ _ h0, hrc, txn.applyChanges_dels]
  have hf : ∀ k, mvcc.findKey k (kvOpStep (.leaseRevoke id) σ).kvs =
      if k ∈ ks then none else mvcc.findKey k σ.kvs := by
    intro k
    rw [hk]
    generalize σ.kvs = s
    induction s with
    | nil => simp [mvcc.findKey]
    | cons v s ih =>
      unfold mvcc.findKey at ih ⊢
      by_cases hv : v.key ∈ ks
      · rw [List.filter_cons_of_neg (by simp [hv]), ih]
        by_cases hkv : v.key = k
        · subst hkv; simp [hv]
        · simp [hkv]
      · rw [List.filter_cons_of_pos (by simp [hv])]
        by_cases hkv : v.key = k
        · subst hkv; simp [hv]
        · simp only [List.find?_cons, hkv, decide_false]; exact ih
  refine ⟨fun k hl => ?_, fun k l hl hne => ?_, fun k hn => ?_, fun i => ?_⟩
  · rw [hf k]
    suffices hks : k ∈ ks by simp [hks]
    unfold leaseOf at hl
    cases hfk : mvcc.findKey k σ.kvs with
    | none => rw [hfk] at hl; cases hl
    | some kv =>
      rw [hfk] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      have hm : kv ∈ σ.kvs := List.mem_of_find?_eq_some hfk
      have hkk : kv.key = k := by unfold mvcc.findKey at hfk; simpa using List.find?_some hfk
      exact List.mem_map.2 ⟨kv, List.mem_filter.2 ⟨hm, by simp [hl]⟩, hkk⟩
  · rw [hf k]
    suffices hks : k ∉ ks by simp [hks]
    intro hks
    obtain ⟨v, hv, hvk⟩ := List.mem_map.1 hks
    obtain ⟨hvm, hvl⟩ := List.mem_filter.1 hv
    have := txn.findKey_of_mem_sorted σ.kvs_sorted hvm
    rw [hvk] at this
    unfold leaseOf at hl
    rw [this] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    exact hne (hl ▸ (by simpa using hvl))
  · rw [hf k]; split <;> simp [hn]
  · simp only [kvOpStep, hin, ↓reduceIte]
    show i ∈ LeaseTable.ids (σ.leases.filter _) ↔ _
    unfold LeaseTable.ids
    simp only [List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨p, ⟨hp, hpi⟩, rfl⟩; exact ⟨⟨p, hp, rfl⟩, by simpa using hpi⟩
    · rintro ⟨⟨p, hp, rfl⟩, hne⟩; exact ⟨p, ⟨hp, by simpa using hne⟩, rfl⟩

/-- **A revocation of a lease not in the table** changes nothing. -/
theorem step_revoke_missing (id : w64) (σ : KVState) (hn : id ∉ σ.leases.ids) :
    kvOpStep (.leaseRevoke id) σ = σ := by
  simp [kvOpStep, hn]

end pure

end etcd_authlease
end EtcdGrove
end Perennial

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

/-! ### The cell's state and what every update keeps

The cell's ghost state: the leases the main thread fixed (`ids`: root's `Lz`, then u's `Lu`), the
revisions at which `z/lease`, `a/lease`, `a/txn` were first attached (`ps`, in that order), the ids the
grant updates fired with (`gs`), and whether u's revocation of `Lu` has fired (`d`). -/

/-- Root's lease `Lz` (`ids[0]`). -/
def lzOf (ids : List w64) : w64 := ids.getD 0 (W64 0)
/-- u's lease `Lu` (`ids[1]`). -/
def luOf (ids : List w64) : w64 := ids.getD 1 (W64 0)

/-- **The cell's invariant, purely.** -/
structure CellOk (σ : KVState) (ids : List w64) (ps : List Nat) (gs : List w64) (d : Nat) : Prop where
  x_none : mvcc.findKey xK σ.kvs = none
  ids_len : ids.length ≤ 2
  ps_len : ps.length ≤ 3
  ps_ids : ps.length ≤ ids.length + 1 ∧ (1 ≤ ps.length → 1 ≤ ids.length) ∧ (2 ≤ ps.length → 2 ≤ ids.length)
  lz_ne : 1 ≤ ids.length → lzOf ids ≠ W64 0
  lu_ne : 2 ≤ ids.length → luOf ids ≠ W64 0
  lu_lz : 2 ≤ ps.length → luOf ids ≠ lzOf ids
  d_le : d ≤ 1
  d_len : d = 1 → ps.length = 3
  z_at : 1 ≤ ps.length → leaseOf zK σ.kvs = some (lzOf ids)
  a_at : 2 ≤ ps.length → d = 0 → leaseOf aK σ.kvs = some (luOf ids)
  t_at : 3 ≤ ps.length → d = 0 → leaseOf tK σ.kvs = some (luOf ids)
  hist : ∀ ru, ps[1]? = some ru → ru ≤ σ.rev ∧ leaseOf aK (σ.at ru).kvs = some (luOf ids)
  lu_live : 2 ≤ ps.length → d = 0 → luOf ids ∈ σ.leases.ids
  gone : d = 1 → mvcc.findKey aK σ.kvs = none ∧ mvcc.findKey tK σ.kvs = none
  lu_dead : d = 1 → luOf ids ∉ σ.leases.ids
  live : ∀ g ∈ gs, g ≠ W64 0 → g ∈ σ.leases.ids ∨ (d = 1 ∧ g = luOf ids)

theorem leaseOf_some_findKey {k : GoString} {s : List EtcdKv} {l : w64} (h : leaseOf k s = some l) :
    ∃ kv, mvcc.findKey k s = some kv ∧ kv.lease = l := by
  unfold leaseOf at h
  cases hf : mvcc.findKey k s with
  | none => rw [hf] at h; cases h
  | some kv => rw [hf] at h; exact ⟨kv, rfl, by simpa using h⟩

theorem leaseOf_eq_of_findKey {k : GoString} {s s' : List EtcdKv}
    (h : mvcc.findKey k s' = mvcc.findKey k s) : leaseOf k s' = leaseOf k s := by
  unfold leaseOf; rw [h]

/-- The start: nothing fixed, nothing attached, no key `a/x`. -/
theorem cellOk_start (σ : KVState) (hx : mvcc.findKey xK σ.kvs = none) : CellOk σ [] [] [] 0 := by
  refine ⟨hx, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
    by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- **The main thread fixes the next lease** (`Lz` at no lease fixed, `Lu` at one), an id of `gs`. -/
theorem cellOk_fix (σ : KVState) (ids : List w64) (ps : List Nat) (gs : List w64) (d : Nat) (L : w64)
    (h : CellOk σ ids ps gs d) (hlen : ids.length = ps.length) (hlt : ids.length < 2) (hL : L ≠ W64 0) :
    CellOk σ (ids ++ [L]) ps gs d := by
  have hps : ps.length ≤ 1 := by omega
  have g0 : lzOf (ids ++ [L]) = (if ids.length = 0 then L else lzOf ids) := by
    unfold lzOf; rcases ids with _ | ⟨a, _⟩ <;> simp
  have g1 : ids.length = 1 → luOf (ids ++ [L]) = L := by
    intro h1; obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 h1; rfl
  have l0 : 1 ≤ ids.length → lzOf (ids ++ [L]) = lzOf ids := by
    intro h1; rw [g0]; simp only [show ids.length ≠ 0 by omega, ↓reduceIte]
  refine ⟨h.x_none, by simp; omega, h.ps_len, ⟨by simp; omega, fun _ => by simp, fun h2 => by omega⟩,
    fun _ => ?_, fun h2 => ?_, fun h2 => by omega, h.d_le, fun hd => by have := h.d_len hd; omega,
    fun h1 => ?_, fun h2 => by omega, fun h3 => by omega, fun ru hru => ?_, fun h2 => by omega,
    h.gone, fun hd => by have := h.d_len hd; omega, fun g hg hg0 => ?_⟩
  · by_cases h0 : ids.length = 0
    · rw [g0]; simp only [h0, ↓reduceIte]; exact hL
    · rw [l0 (by omega)]; exact h.lz_ne (by omega)
  · simp at h2; rw [g1 (by omega)]; exact hL
  · rw [l0 (h.ps_ids.2.1 h1)]; exact h.z_at h1
  · obtain ⟨hl, -⟩ := List.getElem?_eq_some_iff.1 hru; omega
  · rcases h.live g hg hg0 with h1 | ⟨hd, -⟩
    · exact Or.inl h1
    · have := h.d_len hd; omega

/-- **What a grant's freshness gives the cell**: after the revocation, a grant's id is not `Lu`
(`Lu` was attached to `a/lease` at a revision of the state). -/
theorem cellOk_fresh {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk σ ids ps gs d) (id : w64)
    (hf : ∀ r ≤ σ.rev, ∀ kv ∈ (σ.at r).kvs, kv.lease ≠ W64 0 → kv.lease ≠ id) :
    d = 1 → id ≠ luOf ids := by
  intro hd he
  have h3 := h.d_len hd
  obtain ⟨ru, hru⟩ : ∃ ru, ps[1]? = some ru := ⟨ps[1], List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨hr, hl⟩ := h.hist ru hru
  obtain ⟨kv, hkv, hkl⟩ := leaseOf_some_findKey hl
  exact hf ru hr kv (List.mem_of_find?_eq_some hkv) (by rw [hkl]; exact h.lu_ne (by have := h.ps_ids.2.2; omega))
    (by rw [hkl, he])

/-- **A grant keeps the cell**, its id added to `gs` (its TTL at most the maximum; after the
revocation, its id not `Lu`). -/
theorem cellOk_grant {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk σ ids ps gs d) (id ttl : w64) (httl : sint.Z ttl ≤ maxLeaseTTL)
    (hf : d = 1 → id ≠ luOf ids) :
    CellOk (kvOpStep (.leaseGrant id ttl) σ) ids ps (gs ++ [id]) d := by
  obtain ⟨hkv, hids⟩ := step_grant id ttl σ
  have hrev : (kvOpStep (.leaseGrant id ttl) σ).rev = σ.rev := by
    simp only [kvOpStep]; split <;> rfl
  have hat : ∀ r, (kvOpStep (.leaseGrant id ttl) σ).at r = σ.at r := by
    intro r; simp only [kvOpStep]; split <;> rfl
  refine ⟨hkv ▸ h.x_none, h.ids_len, h.ps_len, h.ps_ids, h.lz_ne, h.lu_ne, h.lu_lz, h.d_le, h.d_len,
    hkv ▸ h.z_at, hkv ▸ h.a_at, hkv ▸ h.t_at, fun ru hru => by rw [hrev, hat]; exact h.hist ru hru,
    fun h2 hd => (hids _).2 (Or.inl (h.lu_live h2 hd)), hkv ▸ h.gone, fun hd hin => ?_,
    fun g hg hg0 => ?_⟩
  · rcases (hids _).1 hin with h1 | ⟨-, h2⟩
    · exact h.lu_dead hd h1
    · exact hf hd h2.symm
  · rcases List.mem_append.1 hg with hg | hg
    · rcases h.live g hg hg0 with h1 | h1
      · exact Or.inl ((hids _).2 (Or.inl h1))
      · exact Or.inr h1
    · rw [List.mem_singleton] at hg; subst hg
      by_cases hok : leaseGrantOk σ.leases g ttl
      · exact Or.inl ((hids _).2 (Or.inr ⟨hok, rfl⟩))
      · have : g ∈ σ.leases.ids := by
          unfold leaseGrantOk at hok
          exact Classical.byContradiction fun hn => hok ⟨hg0, httl, hn⟩
        exact Or.inl ((hids _).2 (Or.inl this))

/-- `Lz` is live whenever it is a grant id (no update removes it). -/
theorem cellOk_lz_live {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk σ ids ps gs d) (h1 : 1 ≤ ids.length) (hg : lzOf ids ∈ gs) : lzOf ids ∈ σ.leases.ids := by
  rcases h.live _ hg (h.lz_ne h1) with h' | ⟨hd, he⟩
  · exact h'
  · exact absurd he.symm (h.lu_lz (by have := h.d_len hd; omega))

theorem leaseMissing_of_mem {σ : KVState} {L : w64} (h : L ∈ σ.leases.ids) : ¬ σ.leaseMissing L :=
  fun hm => hm.2 h

/-- **Root's put of `z/lease` with `Lz` keeps the cell**, recording `z/lease`'s first attachment. -/
theorem cellOk_putZ {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk σ ids ps gs d) (h1 : 1 ≤ ids.length) (hg : lzOf ids ∈ gs) :
    CellOk (kvOpStep (.put (leasePutOp zK (lzOf ids))) σ) ids
      (if ps = [] then [(kvOpStep (.put (leasePutOp zK (lzOf ids))) σ).rev] else ps) gs d := by
  have hlive := cellOk_lz_live h h1 hg
  obtain ⟨hz, hoth, hls⟩ := step_leasePut_live zK (lzOf ids) σ (leaseMissing_of_mem hlive)
  have hle := kvOpStep_rev_le (.put (leasePutOp zK (lzOf ids))) σ
  have hat : ∀ r ≤ σ.rev, (kvOpStep (.put (leasePutOp zK (lzOf ids))) σ).at r = σ.at r :=
    fun r hr => kvOpStep_at _ σ r hr
  generalize kvOpStep (.put (leasePutOp zK (lzOf ids))) σ = σ' at hz hoth hls hle hat ⊢
  have hx : mvcc.findKey xK σ'.kvs = none := by rw [hoth xK (by decide)]; exact h.x_none
  have ha : leaseOf aK σ'.kvs = leaseOf aK σ.kvs := leaseOf_eq_of_findKey (hoth aK (by decide))
  have ht : leaseOf tK σ'.kvs = leaseOf tK σ.kvs := leaseOf_eq_of_findKey (hoth tK (by decide))
  by_cases hp : ps = []
  · subst hp
    have hd : d = 0 := by
      have := h.d_le
      exact Classical.byContradiction fun hd => by have := h.d_len (by omega); simp at this
    simp only [↓reduceIte]
    refine ⟨hx, h.ids_len, by simp, ⟨by simp, fun _ => h1, fun h2 => by simp at h2⟩, h.lz_ne,
      h.lu_ne, fun h2 => by simp at h2, h.d_le, fun hd' => by omega, fun _ => hz,
      fun h2 => by simp at h2, fun h2 => by simp at h2, fun ru hru => by simp at hru,
      fun h2 => by simp at h2, fun hd' => by omega, fun hd' => by omega, fun g hg' hg0 => ?_⟩
    rcases h.live g hg' hg0 with h' | h'
    · exact Or.inl (hls ▸ h')
    · omega
  · simp only [hp, ↓reduceIte]
    refine ⟨hx, h.ids_len, h.ps_len, h.ps_ids, h.lz_ne, h.lu_ne, h.lu_lz, h.d_le, h.d_len,
      fun _ => hz, fun h2 hd => ha ▸ h.a_at h2 hd, fun h3 hd => ht ▸ h.t_at h3 hd, fun ru hru => ?_,
      fun h2 hd => hls ▸ h.lu_live h2 hd, fun hd => ?_, fun hd => hls ▸ h.lu_dead hd,
      fun g hg' hg0 => hls ▸ h.live g hg' hg0⟩
    · obtain ⟨hr, hl⟩ := h.hist ru hru
      exact ⟨by omega, by rw [hat ru hr]; exact hl⟩
    · obtain ⟨g1, g2⟩ := h.gone hd
      exact ⟨by rw [hoth aK (by decide)]; exact g1, by rw [hoth tK (by decide)]; exact g2⟩

/-- **u's put of `a/lease` with `Lu` keeps the cell** (fired after root's put; granted, so `Lu ≠ Lz`:
`z/lease` holds `Lz`, which u may not write), recording `a/lease`'s first attachment; after the
revocation it changes nothing (`Lu` is gone). -/
theorem cellOk_putA {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk σ ids ps gs d) (h1 : 1 ≤ ps.length) (h2 : 2 ≤ ids.length) (hg : luOf ids ∈ gs)
    (hne : luOf ids ≠ lzOf ids) :
    CellOk (kvOpStep (.put (leasePutOp aK (luOf ids))) σ) ids
      (if ps.length = 1 then ps ++ [(kvOpStep (.put (leasePutOp aK (luOf ids))) σ).rev] else ps) gs d := by
  by_cases hd : d = 1
  · have h3 := h.d_len hd
    have hm : σ.leaseMissing (luOf ids) := ⟨h.lu_ne h2, h.lu_dead hd⟩
    rw [step_leasePut_missing _ _ σ hm]
    simp only [show ps.length ≠ 1 by omega, ↓reduceIte]
    exact h
  have hd0 : d = 0 := by have := h.d_le; omega
  have hlive : luOf ids ∈ σ.leases.ids := by
    rcases h.live _ hg (h.lu_ne h2) with h' | ⟨hd', -⟩
    · exact h'
    · omega
  obtain ⟨ha, hoth, hls⟩ := step_leasePut_live aK (luOf ids) σ (leaseMissing_of_mem hlive)
  have hle := kvOpStep_rev_le (.put (leasePutOp aK (luOf ids))) σ
  have hat : ∀ r ≤ σ.rev, (kvOpStep (.put (leasePutOp aK (luOf ids))) σ).at r = σ.at r :=
    fun r hr => kvOpStep_at _ σ r hr
  generalize kvOpStep (.put (leasePutOp aK (luOf ids))) σ = σ' at ha hoth hls hle hat ⊢
  have hx : mvcc.findKey xK σ'.kvs = none := by rw [hoth xK (by decide)]; exact h.x_none
  have hz : leaseOf zK σ'.kvs = leaseOf zK σ.kvs := leaseOf_eq_of_findKey (hoth zK (by decide))
  have ht : leaseOf tK σ'.kvs = leaseOf tK σ.kvs := leaseOf_eq_of_findKey (hoth tK (by decide))
  by_cases hp : ps.length = 1
  · simp only [hp, ↓reduceIte]
    have hlen : (ps ++ [σ'.rev]).length = 2 := by simp [hp]
    refine ⟨hx, h.ids_len, by omega, ⟨by omega, fun _ => by omega, fun _ => h2⟩, h.lz_ne, h.lu_ne,
      fun _ => hne, h.d_le, fun hd' => by omega, fun _ => hz ▸ h.z_at (by omega), fun _ _ => ha,
      fun h3 => by omega, fun ru hru => ?_, fun _ _ => hls ▸ hlive, fun hd' => by omega,
      fun hd' => by omega, fun g hg' hg0 => hls ▸ h.live g hg' hg0⟩
    have : ru = σ'.rev := by
      rw [List.getElem?_append_right (by omega), hp] at hru; simpa using hru.symm
    subst this
    exact ⟨Nat.le_refl _, by rw [KVState.at_rev]; exact ha⟩
  · simp only [hp, ↓reduceIte]
    refine ⟨hx, h.ids_len, h.ps_len, h.ps_ids, h.lz_ne, h.lu_ne, h.lu_lz, h.d_le, h.d_len,
      fun h1' => hz ▸ h.z_at h1', fun _ _ => ha, fun h3 hd' => ht ▸ h.t_at h3 hd', fun ru hru => ?_,
      fun h2' hd' => hls ▸ h.lu_live h2' hd', fun hd' => by omega, fun hd' => by omega,
      fun g hg' hg0 => hls ▸ h.live g hg' hg0⟩
    obtain ⟨hr, hl⟩ := h.hist ru hru
    exact ⟨by omega, by rw [hat ru hr]; exact hl⟩

/-- **u's transaction putting `a/txn` with `Lu` keeps the cell** (fired after u's put), recording
`a/txn`'s first attachment; after the revocation it changes nothing. -/
theorem cellOk_txnT {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk σ ids ps gs d) (h2 : 2 ≤ ps.length) :
    CellOk (kvOpStep (.txn (txnWireOf (leaseTxn tK (luOf ids)))) σ) ids
      (if ps.length = 2 then ps ++ [(kvOpStep (.txn (txnWireOf (leaseTxn tK (luOf ids)))) σ).rev] else ps)
      gs d := by
  have hi2 : 2 ≤ ids.length := h.ps_ids.2.2 h2
  by_cases hd : d = 1
  · have h3 := h.d_len hd
    rw [step_leaseTxn_missing _ _ σ (h.lu_ne hi2) (h.lu_dead hd)]
    simp only [show ps.length ≠ 2 by omega, ↓reduceIte]
    exact h
  have hd0 : d = 0 := by have := h.d_le; omega
  have hlive := h.lu_live h2 hd0
  obtain ⟨ht, hoth, hls⟩ := step_leaseTxn_live tK (luOf ids) σ hlive
  have hle := kvOpStep_rev_le (.txn (txnWireOf (leaseTxn tK (luOf ids)))) σ
  have hat : ∀ r ≤ σ.rev, (kvOpStep (.txn (txnWireOf (leaseTxn tK (luOf ids)))) σ).at r = σ.at r :=
    fun r hr => kvOpStep_at _ σ r hr
  generalize kvOpStep (.txn (txnWireOf (leaseTxn tK (luOf ids)))) σ = σ' at ht hoth hls hle hat ⊢
  have hx : mvcc.findKey xK σ'.kvs = none := by rw [hoth xK (by decide)]; exact h.x_none
  have hz : leaseOf zK σ'.kvs = leaseOf zK σ.kvs := leaseOf_eq_of_findKey (hoth zK (by decide))
  have ha : leaseOf aK σ'.kvs = leaseOf aK σ.kvs := leaseOf_eq_of_findKey (hoth aK (by decide))
  have hhist : ∀ ru, ps[1]? = some ru → ru ≤ σ'.rev ∧ leaseOf aK (σ'.at ru).kvs = some (luOf ids) := by
    intro ru hru
    obtain ⟨hr, hl⟩ := h.hist ru hru
    exact ⟨by omega, by rw [hat ru hr]; exact hl⟩
  by_cases hp : ps.length = 2
  · simp only [hp, ↓reduceIte]
    refine ⟨hx, h.ids_len, by simp [hp], ⟨by simp; omega, fun _ => by omega, fun _ => hi2⟩, h.lz_ne,
      h.lu_ne, fun _ => h.lu_lz h2, h.d_le, fun hd' => by omega,
      fun _ => hz ▸ h.z_at (by omega), fun _ hd' => ha ▸ h.a_at h2 hd', fun _ _ => ht,
      fun ru hru => ?_, fun _ _ => hls ▸ hlive, fun hd' => by omega, fun hd' => by omega,
      fun g hg' hg0 => hls ▸ h.live g hg' hg0⟩
    rw [List.getElem?_append_left (by omega)] at hru
    exact hhist ru hru
  · simp only [hp, ↓reduceIte]
    refine ⟨hx, h.ids_len, h.ps_len, h.ps_ids, h.lz_ne, h.lu_ne, h.lu_lz, h.d_le, h.d_len,
      fun h1' => hz ▸ h.z_at h1', fun h2' hd' => ha ▸ h.a_at h2' hd', fun _ _ => ht, hhist,
      fun h2' hd' => hls ▸ h.lu_live h2' hd', fun hd' => by omega, fun hd' => by omega,
      fun g hg' hg0 => hls ▸ h.live g hg' hg0⟩

/-- **u's revocation of `Lu` keeps the cell** (fired after u's transaction): it deletes `a/lease` and
`a/txn` and removes `Lu`; the cell is then revoked (`d = 1`). -/
theorem cellOk_revokeU {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk σ ids ps gs d) (h3 : ps.length = 3) :
    CellOk (kvOpStep (.leaseRevoke (luOf ids)) σ) ids ps gs 1 := by
  have hi2 : 2 ≤ ids.length := h.ps_ids.2.2 (by omega)
  by_cases hd : d = 1
  · subst hd; rw [step_revoke_missing _ σ (h.lu_dead rfl)]; exact h
  have hd0 : d = 0 := by have := h.d_le; omega
  have hlive := h.lu_live (by omega) hd0
  obtain ⟨hdel, hkeep, hnone, hids⟩ := step_revoke_live (luOf ids) σ hlive
  have hle := kvOpStep_rev_le (.leaseRevoke (luOf ids)) σ
  have hat : ∀ r ≤ σ.rev, (kvOpStep (.leaseRevoke (luOf ids)) σ).at r = σ.at r :=
    fun r hr => kvOpStep_at _ σ r hr
  have hz := h.z_at (by omega)
  have hzk := hkeep zK (lzOf ids) hz (Ne.symm (h.lu_lz (by omega)))
  have ha := hdel aK (h.a_at (by omega) hd0)
  have ht := hdel tK (h.t_at (by omega) hd0)
  have hx := hnone xK h.x_none
  generalize kvOpStep (.leaseRevoke (luOf ids)) σ = σ' at hdel hkeep hnone hids hle hat hzk ha ht hx ⊢
  refine ⟨hx, h.ids_len, h.ps_len, h.ps_ids, h.lz_ne, h.lu_ne, h.lu_lz, by omega, fun _ => h3,
    fun _ => by rw [leaseOf_eq_of_findKey hzk]; exact hz, fun _ h0 => by omega, fun _ h0 => by omega,
    fun ru hru => ?_, fun _ h0 => by omega, fun _ => ⟨ha, ht⟩, fun _ hin => ((hids _).1 hin).2 rfl,
    fun g hg hg0 => ?_⟩
  · obtain ⟨hr, hl⟩ := h.hist ru hru
    exact ⟨by omega, by rw [hat ru hr]; exact hl⟩
  · by_cases he : g = luOf ids
    · exact Or.inr ⟨rfl, he⟩
    · rcases h.live g hg hg0 with h' | ⟨hd', -⟩
      · exact Or.inl ((hids _).2 ⟨h', he⟩)
      · omega

/-- **After the revocation, any revocation of `Lu` changes nothing.** -/
theorem cellOk_revokeLu_done {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64}
    (h : CellOk σ ids ps gs 1) : kvOpStep (.leaseRevoke (luOf ids)) σ = σ :=
  step_revoke_missing _ σ (h.lu_dead rfl)

end pure

end etcd_authlease
end EtcdGrove
end Perennial

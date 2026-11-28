/-
**authlease's cell, purely** (auth-lease S4, item 9): the steps of the operations the driver hands the
server, on the client's KV state (`kvOpStep`): a put of a key with a lease (`grantPut`'s), u's
transaction putting `a/txn` with its lease, a grant, a revocation; the leases they leave on the keys
(`leaseOf`) and the revisions they keep (`kvOpStep_at`). Lean-first (no Rocq counterpart).

Moved here from the authlease example's `authlease/CellModel.lean` (2026-11-27): the multi-machine theorem
reuses it (names and namespace `etcd_authlease` unchanged).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn
public import Proof.go_etcd_io.etcd.client.v3.EtcdModelKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.WinLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthModel
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.Model

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
structure CellOk0 (σ : KVState) (ids : List w64) (ps : List Nat) (gs : List w64) (d : Nat) : Prop where
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
theorem cellOk0_start (σ : KVState) (hx : mvcc.findKey xK σ.kvs = none) : CellOk0 σ [] [] [] 0 := by
  refine ⟨hx, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
    by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- **The main thread fixes the next lease** (`Lz` at no lease fixed, `Lu` at one), an id of `gs`. -/
theorem cellOk0_fix (σ : KVState) (ids : List w64) (ps : List Nat) (gs : List w64) (d : Nat) (L : w64)
    (h : CellOk0 σ ids ps gs d) (hlen : ids.length = ps.length) (hlt : ids.length < 2) (hL : L ≠ W64 0) :
    CellOk0 σ (ids ++ [L]) ps gs d := by
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
theorem cellOk0_fresh {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk0 σ ids ps gs d) (id : w64)
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
theorem cellOk0_grant {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk0 σ ids ps gs d) (id ttl : w64) (httl : sint.Z ttl ≤ maxLeaseTTL)
    (hf : d = 1 → id ≠ luOf ids) :
    CellOk0 (kvOpStep (.leaseGrant id ttl) σ) ids ps (gs ++ [id]) d := by
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
theorem cellOk0_lz_live {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk0 σ ids ps gs d) (h1 : 1 ≤ ids.length) (hg : lzOf ids ∈ gs) : lzOf ids ∈ σ.leases.ids := by
  rcases h.live _ hg (h.lz_ne h1) with h' | ⟨hd, he⟩
  · exact h'
  · exact absurd he.symm (h.lu_lz (by have := h.d_len hd; omega))

theorem leaseMissing_of_mem {σ : KVState} {L : w64} (h : L ∈ σ.leases.ids) : ¬ σ.leaseMissing L :=
  fun hm => hm.2 h

/-- **Root's put of `z/lease` with `Lz` keeps the cell**, recording `z/lease`'s first attachment. -/
theorem cellOk0_putZ {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk0 σ ids ps gs d) (h1 : 1 ≤ ids.length) (hg : lzOf ids ∈ gs) :
    CellOk0 (kvOpStep (.put (leasePutOp zK (lzOf ids))) σ) ids
      (if ps = [] then [(kvOpStep (.put (leasePutOp zK (lzOf ids))) σ).rev] else ps) gs d := by
  have hlive := cellOk0_lz_live h h1 hg
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
theorem cellOk0_putA {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk0 σ ids ps gs d) (h1 : 1 ≤ ps.length) (h2 : 2 ≤ ids.length) (hg : luOf ids ∈ gs)
    (hne : luOf ids ≠ lzOf ids) :
    CellOk0 (kvOpStep (.put (leasePutOp aK (luOf ids))) σ) ids
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
theorem cellOk0_txnT {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk0 σ ids ps gs d) (h2 : 2 ≤ ps.length) :
    CellOk0 (kvOpStep (.txn (txnWireOf (leaseTxn tK (luOf ids)))) σ) ids
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
theorem cellOk0_revokeU {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk0 σ ids ps gs d) (h3 : ps.length = 3) :
    CellOk0 (kvOpStep (.leaseRevoke (luOf ids)) σ) ids ps gs 1 := by
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
theorem cellOk0_revokeLu_done {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64}
    (h : CellOk0 σ ids ps gs 1) : kvOpStep (.leaseRevoke (luOf ids)) σ = σ :=
  step_revoke_missing _ σ (h.lu_dead rfl)

/-! ### The attachments' history -/

/-- A step's revision grows by at most one. -/
theorem kvOpStep_rev_le_succ (op : KVOp) (σ : KVState) : (kvOpStep op σ).rev ≤ σ.rev + 1 := by
  obtain ⟨cs, -, h⟩ := kvOpStep_commit op σ
  by_cases hc : cs = []
  · subst hc; rw [KVState.commit_nil] at h; omega
  · rw [KVState.commit_rev σ cs hc] at h; omega

/-- **The attachments' history**: `z/lease` holds `Lz` at every revision from its first attachment on,
and `a/lease` holds `Lu` at every revision from its first attachment on until the revocation (what the
lessor law's `leaseKeptIn` asks). -/
structure CellHist (σ : KVState) (ids : List w64) (ps : List Nat) (d : Nat) : Prop where
  z_hist : ∀ r0, ps[0]? = some r0 → r0 ≤ σ.rev ∧
    ∀ r, r0 ≤ r → r ≤ σ.rev → leaseOf zK (σ.at r).kvs = some (lzOf ids)
  a_hist : ∀ r1, ps[1]? = some r1 → d = 0 → r1 ≤ σ.rev ∧
    ∀ r, r1 ≤ r → r ≤ σ.rev → leaseOf aK (σ.at r).kvs = some (luOf ids)

/-- **The cell's invariant, purely**: `CellOk0` and the attachments' history. -/
def CellOk (σ : KVState) (ids : List w64) (ps : List Nat) (gs : List w64) (d : Nat) : Prop :=
  CellOk0 σ ids ps gs d ∧ CellHist σ ids ps d

/-- One key's history through a step: held at every revision from `r0` to the state's (or `r0` the
step's new revision: a first attachment), and in the step's current state, it is held at every
revision from `r0` to the new state's. -/
theorem kept_step (op : KVOp) (σ : KVState) (k : GoString) (L : w64) (r0 : Nat)
    (hold : (r0 ≤ σ.rev ∧ ∀ r, r0 ≤ r → r ≤ σ.rev → leaseOf k (σ.at r).kvs = some L) ∨
      r0 = (kvOpStep op σ).rev)
    (hnew : leaseOf k (kvOpStep op σ).kvs = some L) :
    r0 ≤ (kvOpStep op σ).rev ∧
      ∀ r, r0 ≤ r → r ≤ (kvOpStep op σ).rev → leaseOf k ((kvOpStep op σ).at r).kvs = some L := by
  have hle := kvOpStep_rev_le op σ
  have hs := kvOpStep_rev_le_succ op σ
  refine ⟨?_, fun r h1 h2 => ?_⟩
  · rcases hold with ⟨h, -⟩ | h <;> omega
  · by_cases hr : r = (kvOpStep op σ).rev
    · subst hr; exact hnew
    · rcases hold with ⟨h, hh⟩ | h
      · have hr' : r ≤ σ.rev := by omega
        rw [kvOpStep_at op σ r hr']; exact hh r h1 hr'
      · omega

theorem getElem?_prefix {ps ps' : List Nat} (hps : ps <+: ps') {i r : Nat} (h : ps[i]? = some r) :
    ps'[i]? = some r := by
  obtain ⟨t, rfl⟩ := hps
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]; exact h

theorem getElem?_append_new {ps : List Nat} {x i r : Nat} (hi : (ps ++ [x])[i]? = some r)
    (hn : ps[i]? = none) : r = x := by
  have hi1 : ps.length ≤ i := List.getElem?_eq_none_iff.1 hn
  rw [List.getElem?_append_right hi1] at hi
  have : i - ps.length = 0 := by have := (List.getElem?_eq_some_iff.1 hi).1; simp at this; omega
  rw [this] at hi; simp at hi; exact hi.symm

/-- **The history through a step** whose result is a `CellOk0` at attachments `ps'` extending `ps`, the
new ones at the new revision. -/
theorem cellHist_step (op : KVOp) {σ : KVState} {ids : List w64} {ps ps' : List Nat} {gs' : List w64}
    {d d' : Nat} (h0' : CellOk0 (kvOpStep op σ) ids ps' gs' d') (hh : CellHist σ ids ps d)
    (hps : ps <+: ps') (hnew : ∀ (i r : Nat), ps'[i]? = some r → ps[i]? = none → r = (kvOpStep op σ).rev)
    (hd : d' = 0 → d = 0) :
    CellHist (kvOpStep op σ) ids ps' d' := by
  constructor
  · intro r0 h0
    have hl : 1 ≤ ps'.length := by have := (List.getElem?_eq_some_iff.1 h0).1; omega
    refine kept_step op σ zK _ r0 ?_ (h0'.z_at hl)
    cases hp : ps[0]? with
    | none => exact Or.inr (hnew 0 r0 h0 hp)
    | some r0' =>
      have e : r0 = r0' := Option.some.inj (h0.symm.trans (getElem?_prefix hps hp))
      subst e
      exact Or.inl (hh.z_hist r0 hp)
  · intro r1 h1 hd0
    have hl : 2 ≤ ps'.length := by have := (List.getElem?_eq_some_iff.1 h1).1; omega
    refine kept_step op σ aK _ r1 ?_ (h0'.a_at hl hd0)
    cases hp : ps[1]? with
    | none => exact Or.inr (hnew 1 r1 h1 hp)
    | some r1' =>
      have e : r1 = r1' := Option.some.inj (h1.symm.trans (getElem?_prefix hps hp))
      subst e
      exact Or.inl (hh.a_hist r1 hp (hd hd0))

theorem hnew_same {ps : List Nat} {x : Nat} : ∀ (i r : Nat), ps[i]? = some r → ps[i]? = none → r = x :=
  fun _ _ h1 h2 => by rw [h1] at h2; cases h2

theorem cellOk_start (σ : KVState) (hx : mvcc.findKey xK σ.kvs = none) : CellOk σ [] [] [] 0 :=
  ⟨cellOk0_start σ hx, ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩⟩

theorem cellOk_fix (σ : KVState) (ids : List w64) (ps : List Nat) (gs : List w64) (d : Nat) (L : w64)
    (h : CellOk σ ids ps gs d) (hlen : ids.length = ps.length) (hlt : ids.length < 2) (hL : L ≠ W64 0) :
    CellOk σ (ids ++ [L]) ps gs d := by
  refine ⟨cellOk0_fix σ ids ps gs d L h.1 hlen hlt hL, ⟨fun r0 h0 => ?_, fun r1 h1 _ => ?_⟩⟩
  · have hl : 1 ≤ ps.length := by have := (List.getElem?_eq_some_iff.1 h0).1; omega
    have e : lzOf (ids ++ [L]) = lzOf ids := by
      unfold lzOf; rcases ids with _ | ⟨a, _⟩
      · simp at hlen; omega
      · simp
    rw [e]; exact h.2.z_hist r0 h0
  · have := (List.getElem?_eq_some_iff.1 h1).1; omega

theorem cellOk_fresh {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk σ ids ps gs d) (id : w64)
    (hf : ∀ r ≤ σ.rev, ∀ kv ∈ (σ.at r).kvs, kv.lease ≠ W64 0 → kv.lease ≠ id) :
    d = 1 → id ≠ luOf ids :=
  cellOk0_fresh h.1 id hf

theorem cellOk_grant {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk σ ids ps gs d) (id ttl : w64) (httl : sint.Z ttl ≤ maxLeaseTTL)
    (hf : d = 1 → id ≠ luOf ids) :
    CellOk (kvOpStep (.leaseGrant id ttl) σ) ids ps (gs ++ [id]) d :=
  ⟨cellOk0_grant h.1 id ttl httl hf,
    cellHist_step _ (cellOk0_grant h.1 id ttl httl hf) h.2 (List.prefix_refl _) hnew_same _root_.id⟩

theorem cellOk_putZ {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk σ ids ps gs d) (h1 : 1 ≤ ids.length) (hg : lzOf ids ∈ gs) :
    CellOk (kvOpStep (.put (leasePutOp zK (lzOf ids))) σ) ids
      (if ps = [] then [(kvOpStep (.put (leasePutOp zK (lzOf ids))) σ).rev] else ps) gs d := by
  refine ⟨cellOk0_putZ h.1 h1 hg, cellHist_step _ (cellOk0_putZ h.1 h1 hg) h.2 ?_ ?_ _root_.id⟩
  · split
    · rename_i hp; subst hp; exact List.nil_prefix
    · exact List.prefix_refl _
  · intro i r hi hn
    split at hi
    · rename_i hp; subst hp; exact getElem?_append_new (ps := []) hi hn
    · exact hnew_same i r hi hn

theorem cellOk_putA {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk σ ids ps gs d) (h1 : 1 ≤ ps.length) (h2 : 2 ≤ ids.length) (hg : luOf ids ∈ gs)
    (hne : luOf ids ≠ lzOf ids) :
    CellOk (kvOpStep (.put (leasePutOp aK (luOf ids))) σ) ids
      (if ps.length = 1 then ps ++ [(kvOpStep (.put (leasePutOp aK (luOf ids))) σ).rev] else ps) gs d := by
  refine ⟨cellOk0_putA h.1 h1 h2 hg hne, cellHist_step _ (cellOk0_putA h.1 h1 h2 hg hne) h.2 ?_ ?_ _root_.id⟩
  · split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  · intro i r hi hn
    split at hi
    · exact getElem?_append_new hi hn
    · exact hnew_same i r hi hn

theorem cellOk_txnT {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk σ ids ps gs d) (h2 : 2 ≤ ps.length) :
    CellOk (kvOpStep (.txn (txnWireOf (leaseTxn tK (luOf ids)))) σ) ids
      (if ps.length = 2 then ps ++ [(kvOpStep (.txn (txnWireOf (leaseTxn tK (luOf ids)))) σ).rev] else ps)
      gs d := by
  refine ⟨cellOk0_txnT h.1 h2, cellHist_step _ (cellOk0_txnT h.1 h2) h.2 ?_ ?_ _root_.id⟩
  · split
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  · intro i r hi hn
    split at hi
    · exact getElem?_append_new hi hn
    · exact hnew_same i r hi hn

theorem cellOk_revokeU {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk σ ids ps gs d) (h3 : ps.length = 3) :
    CellOk (kvOpStep (.leaseRevoke (luOf ids)) σ) ids ps gs 1 :=
  ⟨cellOk0_revokeU h.1 h3, cellHist_step _ (cellOk0_revokeU h.1 h3) h.2 (List.prefix_refl _) hnew_same
    (fun h => absurd h (by decide))⟩

theorem cellOk_revokeLu_done {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64}
    (h : CellOk σ ids ps gs 1) : kvOpStep (.leaseRevoke (luOf ids)) σ = σ :=
  cellOk0_revokeLu_done h.1

/-! ### A put of another key, without a lease (`SetUp`'s puts) -/

/-- **A put without a lease of the key `k`**: the other keys kept, the table kept. -/
theorem step_put0 (k v : GoString) (σ : KVState) :
    (∀ k', k' ≠ k → mvcc.findKey k' (kvOpStep (.put (txn.putOpOf k v (W64 0) false false false)) σ).kvs =
        mvcc.findKey k' σ.kvs) ∧
      (kvOpStep (.put (txn.putOpOf k v (W64 0) false false false)) σ).leases = σ.leases := by
  have hl : ¬ σ.leaseMissing (0#64) := fun hm => hm.1 rfl
  have hk : (kvOpStep (.put (txn.putOpOf k v (W64 0) false false false)) σ).kvs =
      putKv (W64 ((σ.rev + 1 : Nat) : Int)) k v (W64 0) σ.kvs := by
    simp [kvOpStep, hl, KVState.commit_kvs, txn.needsPrev, mvcc.applyChanges, mvcc.applyChange,
      txn.putChangeOf, txn.putValOf, txn.putLeaseOf, txn.putOpOf]
  refine ⟨fun k' hne => ?_, ?_⟩
  · rw [hk]; exact findKey_putKv_ne σ.kvs_sorted _ _ _ _ _ (Ne.symm hne)
  · simp [kvOpStep, hl, KVState.commit]; split <;> rfl

/-- **A put without a lease of a key other than the cell's four keeps the cell** (nothing recorded). -/
theorem cellOk0_put0 {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk0 σ ids ps gs d) (k v : GoString) (hx : k ≠ xK) (hz : k ≠ zK) (ha : k ≠ aK) (ht : k ≠ tK) :
    CellOk0 (kvOpStep (.put (txn.putOpOf k v (W64 0) false false false)) σ) ids ps gs d := by
  obtain ⟨hoth, hls⟩ := step_put0 k v σ
  have hle := kvOpStep_rev_le (.put (txn.putOpOf k v (W64 0) false false false)) σ
  have hat : ∀ r ≤ σ.rev, (kvOpStep (.put (txn.putOpOf k v (W64 0) false false false)) σ).at r = σ.at r :=
    fun r hr => kvOpStep_at _ σ r hr
  generalize kvOpStep (.put (txn.putOpOf k v (W64 0) false false false)) σ = σ' at hoth hls hle hat ⊢
  have lz : leaseOf zK σ'.kvs = leaseOf zK σ.kvs := leaseOf_eq_of_findKey (hoth zK (Ne.symm hz))
  have la : leaseOf aK σ'.kvs = leaseOf aK σ.kvs := leaseOf_eq_of_findKey (hoth aK (Ne.symm ha))
  have lt : leaseOf tK σ'.kvs = leaseOf tK σ.kvs := leaseOf_eq_of_findKey (hoth tK (Ne.symm ht))
  refine ⟨by rw [hoth xK (Ne.symm hx)]; exact h.x_none, h.ids_len, h.ps_len, h.ps_ids, h.lz_ne, h.lu_ne,
    h.lu_lz, h.d_le, h.d_len, fun h1 => lz ▸ h.z_at h1, fun h2 hd => la ▸ h.a_at h2 hd,
    fun h3 hd => lt ▸ h.t_at h3 hd, fun ru hru => ?_, fun h2 hd => hls ▸ h.lu_live h2 hd, fun hd => ?_,
    fun hd => hls ▸ h.lu_dead hd, fun g hg hg0 => hls ▸ h.live g hg hg0⟩
  · obtain ⟨hr, hl⟩ := h.hist ru hru
    exact ⟨by omega, by rw [hat ru hr]; exact hl⟩
  · obtain ⟨g1, g2⟩ := h.gone hd
    exact ⟨by rw [hoth aK (Ne.symm ha)]; exact g1, by rw [hoth tK (Ne.symm ht)]; exact g2⟩

theorem cellOk_put0 {σ : KVState} {ids : List w64} {ps : List Nat} {gs : List w64} {d : Nat}
    (h : CellOk σ ids ps gs d) (k v : GoString) (hx : k ≠ xK) (hz : k ≠ zK) (ha : k ≠ aK) (ht : k ≠ tK) :
    CellOk (kvOpStep (.put (txn.putOpOf k v (W64 0) false false false)) σ) ids ps gs d :=
  ⟨cellOk0_put0 h.1 k v hx hz ha ht,
    cellHist_step _ (cellOk0_put0 h.1 k v hx hz ha ht) h.2 (List.prefix_refl _) hnew_same _root_.id⟩

/-! ### The lease checks at the set-up's auth state -/

/-- A key with a nonzero lease is in the state's lease items. -/
theorem leaseItemsOf_of_leaseOf {k : GoString} {s : List EtcdKv} {l : w64} (h : leaseOf k s = some l)
    (hl : l ≠ W64 0) : (mvcc.leaseItemsOf s).lookup ⟨k⟩ = some l := by
  show (mvcc.findKey k s).bind mvcc.kvLease = some l
  obtain ⟨kv, hkv, hkl⟩ := leaseOf_some_findKey h
  rw [hkv]
  simp only [Option.bind_some, mvcc.kvLease]
  simp only [hkl, hl, ↓reduceIte]

/-- **The lease check at `setupSt` fails** for a lease holding the key `k`, a principal whose user is
empty, `u` or `v`, and `k` not one `u` may write (when the user is `u`). -/
theorem not_leaseOk_setupSt (r : Nat) (a : go_etcd_io.etcd.server.v3.auth.AuthInfo)
    (I : GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64) (k : GoString) (L : w64)
    (hI : I.lookup ⟨k⟩ = some L)
    (hu : a.Username' = (zeroValDef : GoString) ∨ (a.Username' = go!"u" ∧ ¬ etcd_auth.inRangeK k) ∨
      a.Username' = go!"v") :
    ¬ leaseOk (etcd_auth.setupSt r) a I L := by
  have h0 : (etcd_auth.setupSt r).users !! (zeroValDef : GoString) = none := by
    simp [etcd_auth.setupSt, zeroValDef]
  intro hok
  unfold leaseOk at hok
  rcases hok with hen | hadm | hall
  · simp [etcd_auth.setupSt] at hen
  · unfold auth.adminOk at hadm
    rcases hadm with hen | ⟨a', u', ha, -, hus, hroot⟩
    · simp [etcd_auth.setupSt] at hen
    cases ha
    simp only [auth.authInfoM] at hus
    rcases hu with hz | ⟨hu', -⟩ | hv
    · rw [hz, h0] at hus; cases hus
    · rw [hu', etcd_auth.setupSt_users_u] at hus; cases hus; exact etcd_auth.not_isRoot_u hroot
    · rw [hv, etcd_auth.setupSt_users_v] at hus; cases hus; exact etcd_auth.not_isRoot_v hroot
  · obtain ⟨-, -, u', hus, hc⟩ := hall k hI
    simp only [auth.authInfoM] at hus
    rcases hu with hz | ⟨hu', hk⟩ | hv
    · rw [hz, h0] at hus; cases hus
    · rw [hu', etcd_auth.setupSt_users_u] at hus; cases hus
      rcases hc with hroot | hc
      · exact etcd_auth.not_isRoot_u hroot
      · have hc := (auth.coversX_point_iff _ _ _ _ (etcd_auth.setupSt_permKeysOk r)).1 hc
        simp only [auth.coversPoint, etcd_auth.userPerms_u, List.mem_singleton, exists_eq_left] at hc
        exact hk ((etcd_auth.permR_covers _ k).1 hc)
    · rw [hv, etcd_auth.setupSt_users_v] at hus; cases hus
      rcases hc with hroot | hc
      · exact etcd_auth.not_isRoot_v hroot
      · have hc := (auth.coversX_point_iff _ _ _ _ (etcd_auth.setupSt_permKeysOk r)).1 hc
        simp [auth.coversPoint, etcd_auth.userPerms_v] at hc

/-- `z/lease` is not in `[a, b)`: u may not write it. -/
theorem not_inRangeK_zK : ¬ etcd_auth.inRangeK zK := by
  unfold etcd_auth.inRangeK
  decide

end pure

end etcd_authlease
end EtcdGrove
end Perennial

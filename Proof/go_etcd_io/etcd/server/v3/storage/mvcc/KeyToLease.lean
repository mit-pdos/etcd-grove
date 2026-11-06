/-
**`restore`'s map of keys to leases** (2026-11-06; until then `restore` was specified only over
entries without a lease). Lean-first (no Rocq counterpart). Pure.

`restoreChunk` updates `keyToLease` per entry of the `Key` bucket, in order: a tombstone, or a put
without a lease, deletes the key; a put with a lease sets it (`ktlStep`). `ktlApply M ents` is the
map after the entries `ents` from `M`. `ktlItems M ks` is the lessor's item map after
`restore`'s `Attach` of the keys `ks` (in order) of `M` to their leases, from the empty one.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreRecs
public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- One entry's update of `keyToLease` (`restoreChunk`'s branches). -/
def mvcc.ktlStep (M : GMap GoString w64) (e : mvcc.KvEnt) : GMap GoString w64 :=
  if e.tomb then GMap.delete e.kv.key M
  else if e.kv.lease = W64 0 then GMap.delete e.kv.key M
  else GMap.insert e.kv.key e.kv.lease M

/-- The map after the entries `ents`, in order. -/
def mvcc.ktlApply (M : GMap GoString w64) (ents : List mvcc.KvEnt) : GMap GoString w64 :=
  ents.foldl mvcc.ktlStep M

theorem mvcc.ktlApply_nil (M : GMap GoString w64) : mvcc.ktlApply M [] = M := rfl

theorem mvcc.ktlApply_append (M : GMap GoString w64) (a b : List mvcc.KvEnt) :
    mvcc.ktlApply M (a ++ b) = mvcc.ktlApply (mvcc.ktlApply M a) b := by
  unfold mvcc.ktlApply; exact List.foldl_append

theorem mvcc.ktlApply_snoc (M : GMap GoString w64) (a : List mvcc.KvEnt) (e : mvcc.KvEnt) :
    mvcc.ktlApply M (a ++ [e]) = mvcc.ktlStep (mvcc.ktlApply M a) e := by
  rw [mvcc.ktlApply_append]; rfl

/-- With no entry leased, the map from `∅` stays empty. -/
theorem mvcc.ktlApply_noLease (ents : List mvcc.KvEnt) (h : ∀ e ∈ ents, e.kv.lease = W64 0) :
    mvcc.ktlApply (∅ : GMap GoString w64) ents = ∅ := by
  unfold mvcc.ktlApply
  suffices ∀ (es : List mvcc.KvEnt), (∀ e ∈ es, e.kv.lease = W64 0) →
      es.foldl mvcc.ktlStep (∅ : GMap GoString w64) = ∅ from this ents h
  intro es
  induction es with
  | nil => intro _; rfl
  | cons e es ih =>
    intro he
    simp only [List.foldl_cons]
    have h0 : mvcc.ktlStep (∅ : GMap GoString w64) e = ∅ := by
      unfold mvcc.ktlStep
      rw [he e (by simp)]
      split <;> simp [GMap.delete_empty]
    rw [h0]
    exact ih (fun e' h' => he e' (by simp [h']))

section items
variable [GooseExts]

/-- The lessor's item map after `Attach`ing the keys `ks` of `M`, in order, each to its lease
(`restore`'s loop over `keyToLease`), from the empty map. -/
def mvcc.ktlItems (M : GMap GoString w64) (ks : List GoString) :
    GMap go_etcd_io.etcd.server.v3.lease.LeaseItem w64 :=
  ⟨fun it => if it.Key' ∈ ks then M.lookup it.Key' else none,
   ⟨ks.map (fun k => go_etcd_io.etcd.server.v3.lease.LeaseItem.mk k), by
     intro it h
     by_cases hk : it.Key' ∈ ks
     · exact List.mem_map.2 ⟨it.Key', hk, by cases it; rfl⟩
     · simp [hk] at h⟩⟩

theorem mvcc.ktlItems_lookup (M : GMap GoString w64) (ks : List GoString)
    (it : go_etcd_io.etcd.server.v3.lease.LeaseItem) :
    (mvcc.ktlItems M ks).lookup it = if it.Key' ∈ ks then M.lookup it.Key' else none := rfl

theorem mvcc.ktlItems_nil (M : GMap GoString w64) : mvcc.ktlItems M [] = ∅ := by
  apply GMap.ext; intro it; rw [mvcc.ktlItems_lookup]; simp

theorem mvcc.ktlItems_snoc (M : GMap GoString w64) (ks : List GoString) (k : GoString) (l : w64)
    (h : M.lookup k = some l) :
    mvcc.ktlItems M (ks ++ [k]) = lease.insertAll (mvcc.ktlItems M ks) [⟨k⟩] l := by
  apply GMap.ext
  intro it
  show (if it.Key' ∈ ks ++ [k] then M.lookup it.Key' else none) =
    (if (⟨k⟩ : go_etcd_io.etcd.server.v3.lease.LeaseItem) = it then some l
      else (if it.Key' ∈ ks then M.lookup it.Key' else none))
  by_cases h1 : it.Key' = k
  · have : it = ⟨k⟩ := by cases it; simp_all
    subst this; simp [h]
  · have : (⟨k⟩ : go_etcd_io.etcd.server.v3.lease.LeaseItem) ≠ it := by
      intro h'; subst h'; exact h1 rfl
    simp [this, h1]

end items

end EtcdGrove
end Perennial

/-
**`restore`'s map of keys to leases** (2026-11-06; until then `restore` was specified only over
entries without a lease). Lean-first (no Rocq counterpart). Pure.

`restoreChunk` updates `keyToLease` per entry of the `Key` bucket, in order: a tombstone, or a put
without a lease, deletes the key; a put with a lease sets it (`ktlStep`). `ktlApply M ents` is the
map after the entries `ents` from `M`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.RestoreRecs

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

end EtcdGrove
end Perennial

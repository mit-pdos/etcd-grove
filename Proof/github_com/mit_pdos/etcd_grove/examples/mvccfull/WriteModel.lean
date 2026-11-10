/-
The tester's model of a write against mvcc's (pure; `notes/mvccfull-proof-plan.md`;
ported from mvccrand's). Lean-first (no Rocq counterpart).

**The probe of the write contracts**: the writer's pending model (`PendM`, `Pending.lean`) of a
put and of a range delete is mvcc's (`applyChange`, the client model's `putKv`; `delKeys`):

- `stMatch_put`: a put's record (`putRec`: the create revision and version kept and bumped, or
  created at the revision) is `putKv`'s key-value;
- `stMatch_del`: a delete removes the key from both;
- `delKeys_eq_match`: the keys `Txn.DeleteRange.contract` deletes (`delKeys`, the index's answers
  at the pending revision, unlimited) are exactly the keys `pending.del` deletes (`matchKeys`, the
  tester's keys in its order, present and in the range), for a well-formed log.

So the writer's checks of `Put`'s and `DeleteRange`'s results, and its model of the states it
appends, follow from the contracts.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Pending

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc

section model
variable [GooseExts]

theorem findKey_filter_ne (s : List EtcdKv) (k x : GoString) (hx : x ≠ k) :
    findKey x (s.filter (fun y => !decide (y.key = k))) = findKey x s := by
  unfold findKey
  induction s with
  | nil => rfl
  | cons y s ih =>
    by_cases hy : y.key = k
    · have : k ≠ x := Ne.symm hx
      simp [List.filter, hy, this, ih]
    · simp only [List.filter, hy, decide_false, Bool.not_false, List.find?_cons]
      split <;> simp_all

theorem findKey_filter_eq (s : List EtcdKv) (k : GoString) :
    findKey k (s.filter (fun y => !decide (y.key = k))) = none := by
  unfold findKey
  rw [List.find?_eq_none]
  intro y hy
  have := (List.mem_filter.1 hy).2
  simpa using this

/-- **A delete removes the key from the tester's map and from the store's state.** -/
theorem stMatch_del (ks : List GoString) (M : GMap GoString kvRec) (s : List EtcdKv) (r : w64)
    (k : GoString) (hM : stMatch ks M s) : stMatch ks (GMap.delete k M) (applyChange r s (.del k)) := by
  refine ⟨fun x => ?_, fun w hw => hM.2 w (List.mem_filter.1 hw).1⟩
  simp only [applyChange]
  by_cases hx : x = k
  · subst hx; rw [findKey_filter_eq]; simp
  · rw [findKey_filter_ne s k x hx, GMap.lookup_delete_ne _ (Ne.symm hx)]; exact hM.1 x

/-- **A put's record is the store's key-value** (`putRec` is `putKv`'s). -/
theorem stMatch_put (ks : List GoString) (M : GMap GoString kvRec) (s : List EtcdKv) (hs : s.Pairwise etcdKvLess)
    (r : w64) (k v : GoString) (l : w64) (hM : stMatch ks M s) (hk : k ∈ ks) :
    stMatch ks (<[k := putRec M r k v l]> M) (applyChange r s (.put k v l)) := by
  simp only [applyChange]
  refine ⟨fun x => ?_, fun w hw => ?_⟩
  · by_cases hx : x = k
    · subst hx
      rw [findKey_putKv_self_eq hs, GMap.lookup_insert, hM.1 x]
      unfold putRec
      cases M !! x <;> rfl
    · rw [findKey_putKv_other hs r x k v l (Ne.symm hx), GMap.lookup_insert_ne _ _ (Ne.symm hx)]
      exact hM.1 x
  · unfold putKv at hw
    rcases btInsert_mem hw with h | h
    · subst h
      split
      · rename_i w' hw'
        exact hM.2 w' (List.mem_of_find?_eq_some hw')
      · exact hk
    · exact hM.2 w h

/-- **The keys a range delete deletes are the tester's** (`delKeys`, unlimited answers at the
pending revision, against `matchKeys` of the pending state). -/
theorem delKeys_eq_match (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) (L : Log)
    (pend : List Change) (hne : L ≠ [])
    (hok : txn.LogOk (L ++ [pend])) (endNil : Bool) (k e : GoString)
    (M : GMap GoString kvRec) (hM : stMatch ks M (applyChanges (W64 L.length) (stateAfter L) pend)) :
    delKeys L pend endNil k e = matchKeys ks M endNil k e := by
  unfold delKeys
  rw [txn.rangeTaken_eq]
  have hlim : limitOf (W64 0) = none := by unfold limitOf; simp
  rw [hlim]
  simp only [takeLimit]
  have hwr : writeRev L pend < 2 ^ 63 := by
    have := writeRev_lt L pend hne
    have := hok.2
    omega
  have h := answers_keys_eq_match ks hks (L ++ [pend]) hok endNil k e (writeRev L pend) hwr M
    (by rw [stateAt_writeRev L pend hne]; exact hM)
  exact h

end model

end mvccfull
end EtcdGrove
end Perennial

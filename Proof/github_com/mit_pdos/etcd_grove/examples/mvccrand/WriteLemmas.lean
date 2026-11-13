/-
The writer's single-operation transactions (`put`, `deleteRange`): their shared pure lemmas.
Lean-first (no Rocq counterpart).

- The model at the transaction's start (`pendOk_nil`'s parts): the last revision's state is the
  store's (`stMatch_lastSt`, from `writerIdle`'s `revOk`), and so are the states a read in the
  transaction sees before a change (`viewSt_match_nil`);
- one put, one range delete keep `pendOk` (`pendOk_put`, `pendOk_del`);
- the lessor's items after the commit are the pending ones (`pendItems_commit`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WriteModel
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section model
variable [GooseExts]

/-- The tester's keys are short. -/
theorem keyList_short (k : GoString) (hk : k ∈ keyList) : k.length ≤ 2 := by
  simp only [keyList, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **The last revision's state is the store's** (`writerIdle`'s `revOk` at the last revision). -/
theorem stMatch_lastSt (σ : MvccState) (Hs : List HRev) (hlen : Hs.length = σ.log.length)
    (h1 : 1 ≤ σ.log.length)
    (hrev : ∀ r < Hs.length, ∃ e, Hs[r]? = some e ∧ revOk σ.log Hs r e) :
    stMatch (lastSt Hs) (stateAfter σ.log) := by
  obtain ⟨e, he, hok, -⟩ := hrev (Hs.length - 1) (by omega)
  have hl : lastSt Hs = e.1 := by unfold lastSt; rw [he]; rfl
  rw [hl, ← stateAt_last, ← hlen]
  exact hok

/-- **The states a read sees before the transaction's first change** are the store's, at the read
log `σ.log ++ [[]]` (`Txn.Range`'s at `.write σ []`). -/
theorem viewSt_match_nil (σ : MvccState) (Hs : List HRev) (P : PendM) (hc : P.chs = [])
    (hlen : Hs.length = σ.log.length)
    (hrev : ∀ r < Hs.length, ∃ e, Hs[r]? = some e ∧ revOk σ.log Hs r e) :
    ∀ r : Nat, r < Hs.length → ∃ M, (viewSt Hs P)[r]? = some M ∧ stMatch M (stateAt (σ.log ++ [[]]) r) := by
  intro r hr
  obtain ⟨e, he, hok, -⟩ := hrev r hr
  refine ⟨e.1, ?_, ?_⟩
  · unfold viewSt; simp only [hc, ↓reduceIte, List.append_nil, List.getElem?_map, he]; rfl
  · rw [stateAt_append_lt _ _ (by omega)]; exact hok

theorem viewSt_length_nil (Hs : List HRev) (P : PendM) (hc : P.chs = []) :
    (viewSt Hs P).length = Hs.length := by
  unfold viewSt; simp [hc]

/-- Deleting keys from both sides keeps the match. -/
theorem stMatch_delAll (ks : List GoString) (M : GMap GoString kvRec) (s : List EtcdKv) (r : w64)
    (hM : stMatch M s) : stMatch (delAll ks M) (applyChanges r s (ks.map Change.del)) := by
  induction ks generalizing M s with
  | nil => exact hM
  | cons k ks ih =>
    have := ih (GMap.delete k M) (applyChange r s (.del k)) (stMatch_del M s r k hM)
    simpa only [delAll, applyChanges, List.map_cons, List.foldl_cons] using this

/-- **A range delete in a transaction without changes keeps the model** (`pending.del`'s keys being
`Txn.DeleteRange.contract`'s, `delKeys_eq_match`). -/
theorem pendOk_del (σ : MvccState) (Hs : List HRev) (endNil : Bool) (kk e : GoString)
    (hM : stMatch (lastSt Hs) (stateAfter σ.log))
    (hks : delKeys σ.log [] endNil kk e = matchKeys (lastSt Hs) endNil kk e) :
    pendOk σ Hs ((delKeys σ.log [] endNil kk e).map Change.del)
      ((⟨W64 (Hs.length : Int), lastSt Hs, []⟩ : PendM).del endNil kk e) := by
  rw [hks]
  refine ⟨?_, ?_⟩
  · rw [PendM.del_eq_foldl]; rfl
  · exact stMatch_delAll _ _ _ _ hM

/-- **A put in a transaction without changes keeps the model** (`stMatch_put`). -/
theorem pendOk_put (σ : MvccState) (Hs : List HRev) (hlen : Hs.length = σ.log.length)
    (hM : stMatch (lastSt Hs) (stateAfter σ.log)) (k v : GoString) (l : w64) (hk : k ∈ keyList) :
    pendOk σ Hs [.put k v l] ((⟨W64 (Hs.length : Int), lastSt Hs, []⟩ : PendM).put k v l) := by
  refine ⟨?_, ?_⟩
  · have := pendOf_put (lastSt Hs) (W64 (Hs.length : Int)) [] k v l
    simpa only [List.nil_append, pendOf_nil] using this.symm
  · have hs : (stateAfter σ.log).Pairwise etcdKvLess := by
      rw [← stateAt_last]; exact stateAt_sorted _ _
    have := stMatch_put (lastSt Hs) (stateAfter σ.log) hs (W64 (Hs.length : Int)) k v l hM hk
    rw [hlen] at this
    simpa only [PendM.put, applyChanges, List.foldl_cons, List.foldl_nil, hlen] using this

/-- **The lessor's items after the commit are the pending ones.** -/
theorem pendItems_commit (σ : MvccState) (pend : List Change) :
    pendItems (commitSt σ pend).log [] = pendItems σ.log pend := by
  unfold commitSt MvccState.commitPending MvccState.notify commitLog
  by_cases hp : pend = []
  · subst hp; simp
  · simp only [hp, ↓reduceIte, Option.getD_some]
    rw [pendItems_nil, stateAfter_append]

/-- A positive length's predecessor as a word. -/
theorem w64_pred (n : Nat) (h : 1 ≤ n) (hn : n < 2 ^ 63) :
    W64 (((n - 1 : Nat)) : Int) = W64 (n : Int) - W64 1 := by
  have : ((n - 1 : Nat) : Int) = (n : Int) - 1 := by omega
  rw [this]; word

end model

end mvccrand
end EtcdGrove
end Perennial

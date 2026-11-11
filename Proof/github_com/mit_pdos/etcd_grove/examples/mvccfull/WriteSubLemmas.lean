/-
The writer's sub-operations of a write transaction (pure; mvccrand's `writer.writeOp`'s model
section, over mvccfull's keys `ks`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriteModel
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.EndLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section model
variable [GooseExts]

theorem applyChanges_append' (r : w64) (s : List EtcdKv) (a b : List Change) :
    applyChanges r s (a ++ b) = applyChanges r (applyChanges r s a) b := by
  simp only [applyChanges, List.foldl_append]

theorem pendOk_chs_length {ks : List GoString} {σ : mvcc.api.MvccState} {Hs : List HRev}
    {pend : List Change} {P : PendM} (hok : pendOk ks σ Hs pend P) : P.chs.length = pend.length := by
  rw [hok.1]; exact pendOf_chs_length _ _ _

/-- Deleting keys from both sides keeps the match. -/
theorem stMatch_delAll' (ks : List GoString) (dks : List GoString) (M : GMap GoString kvRec)
    (s : List EtcdKv) (r : w64) (hM : stMatch ks M s) :
    stMatch ks (delAll dks M) (applyChanges r s (dks.map Change.del)) := by
  induction dks generalizing M s with
  | nil => exact hM
  | cons k dks ih =>
    have := ih (GMap.delete k M) (applyChange r s (.del k)) (stMatch_del ks M s r k hM)
    simpa only [delAll, applyChanges, List.map_cons, List.foldl_cons] using this

/-- A put keeps the model, at any pending state. -/
theorem pendOk_put' (ks : List GoString) (σ : mvcc.api.MvccState) (Hs : List HRev)
    (pend : List Change) (P : PendM) (hok : pendOk ks σ Hs pend P)
    (hlen : Hs.length = σ.log.length) (k v : GoString) (l : w64) (hk : k ∈ ks) :
    pendOk ks σ Hs (pend ++ [.put k v l]) (P.put k v l) := by
  have hrev : P.rev = W64 (σ.log.length : Int) := by rw [pendOk_rev' hok, hlen]
  obtain ⟨hP, hst⟩ := hok
  refine ⟨by rw [pendOf_put, ← hP], ?_⟩
  have hs : (applyChanges (W64 (σ.log.length : Int)) (stateAfter σ.log) pend).Pairwise
      etcdKvLess := by
    rw [← stateAt_pend]; exact stateAt_sorted _ _
  have := stMatch_put ks P.st _ hs (W64 (σ.log.length : Int)) k v l hst hk
  rw [applyChanges_append']
  simpa only [PendM.put, hrev, applyChanges, List.foldl_cons, List.foldl_nil] using this

/-- A range delete keeps the model, at any pending state. -/
theorem pendOk_del' (ks : List GoString) (σ : mvcc.api.MvccState) (Hs : List HRev)
    (pend : List Change) (P : PendM) (hok : pendOk ks σ Hs pend P) (endNil : Bool) (kk e : GoString)
    (hks : delKeys σ.log pend endNil kk e = matchKeys ks P.st endNil kk e) :
    pendOk ks σ Hs (pend ++ (delKeys σ.log pend endNil kk e).map Change.del)
      (P.del ks endNil kk e) := by
  obtain ⟨hP, hst⟩ := hok
  rw [hks]
  refine ⟨?_, ?_⟩
  · rw [PendM.del_eq_foldl, pendOf_append, ← hP]
  · rw [applyChanges_append']
    exact stMatch_delAll' _ _ _ _ _ hst

/-- A put keeps the read log's `LogOk`. -/
theorem logOk_put' (L : Log) (pend : List Change) (hok : txn.LogOk (L ++ [pend]))
    (hne : L ≠ []) (hpl : pend.length + 1 < 2 ^ 63) (k v : GoString) (l : w64) :
    txn.LogOk (L ++ [pend ++ [.put k v l]]) := by
  refine txn.LogOk.of_cert ⟨LogWf'.append_change (LogWf'.of_wf hok.wf) hne (.put k v l)
    (fun _ h => by cases h), ?_, ?_⟩ (by simp)
  · have := hok.len; simpa using this
  · intro cs hcs
    simp only [List.mem_append, List.mem_singleton] at hcs
    rcases hcs with h | h
    · exact hok.cs cs (by simp [h])
    · subst h; simp; omega

/-- The keys present and in a range: at most the tester's keys. -/
theorem matchKeys_length_le' (ks : List GoString) (M : GMap GoString kvRec) (endNil : Bool)
    (kk e : GoString) : (matchKeys ks M endNil kk e).length ≤ ks.length := by
  unfold matchKeys; exact List.length_filter_le _ _

end model

end mvccfull
end EtcdGrove
end Perennial

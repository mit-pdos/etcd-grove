/-
Pure lemmas for `shared.Rollback` (U2, `notes/bbolt-proof-plan.md`).

**Spec defect (`Model/FL.lean`'s `FLPg.rollback`).** When `txid` has no pending entry, Go's
`Rollback` returns at once (`txp == nil`), leaving `allocs` as it is, while `FLPg.rollback`
still drops `txid`'s allocations from `allocs`. `FLPg.rollbackGo` is the model of the code: no
change without a pending entry, `FLPg.rollback` otherwise. (A writer that allocated pages but
freed none and rolls back leaves stale `allocs` entries; harmless, since a later `Allocate` of
those pages overwrites them.)
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

/-- `Rollback(txid)` as the code does it: nothing without a pending entry for `txid`. -/
def FLPg.rollbackGo (fl : FLPg) (txid : w64) : FLPg :=
  if fl.pending !! txid = none then fl else fl.rollbackEntry txid

theorem FLPg.rollbackGo_eq (fl : FLPg) (txid : w64) : fl.rollbackGo txid = fl.rollback txid :=
  rfl

/-- A pending entry's (id, allocating transaction) pairs. -/
def Pending.pairs (pd : Pending) : List (w64 × w64) := pd.ids.zip pd.alloctx

/-- One pair of a rolled-back entry: its page is allocated again by its transaction, if known. -/
def rbStep (m : GMap w64 w64) (x : w64 × w64) : GMap w64 w64 :=
  if x.2 = W64 0 then m else <[x.1 := x.2]> m

theorem foldl_rbStep (txid : w64) (l : List (w64 × w64)) (h : ∀ x ∈ l, x.2 ≠ txid)
    (m : GMap w64 w64) :
    l.foldl rbStep m = (l.filter fun x => decide (x.2 ≠ 0 ∧ x.2 ≠ txid)).foldl
      (fun m x => m.insert x.1 x.2) m := by
  induction l generalizing m with
  | nil => rfl
  | cons x l ih =>
    have hx := h x (List.mem_cons_self ..)
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases h0 : x.2 = W64 0
    · simp only [List.foldl_cons, rbStep, h0, ite_true, List.filter_cons]
      rw [ih']; simp [h0]
    · simp only [List.foldl_cons, rbStep, h0, ite_false, List.filter_cons]
      rw [ih', if_pos (decide_eq_true ⟨h0, hx⟩)]; rfl

theorem rollbackGo_some {fl : FLPg} {txid : w64} {pd : Pending} (h : fl.pending !! txid = some pd)
    (hn : txid ∉ pd.alloctx) :
    fl.rollbackGo txid = { fl with
      pending := fl.pending.delete txid,
      allocs := (pd.pairs.foldl rbStep fl.allocs).filter fun _ t => decide (t ≠ txid) } := by
  unfold FLPg.rollbackGo FLPg.rollbackEntry
  rw [if_neg (by simp [h])]
  simp only [h, Option.getD_some]
  rw [foldl_rbStep txid pd.pairs (fun x hx e => hn (e ▸ (List.of_mem_zip hx).2))]
  rfl

theorem rollbackGo_none {fl : FLPg} {txid : w64} (h : fl.pending !! txid = none) :
    fl.rollbackGo txid = fl := by
  unfold FLPg.rollbackGo; rw [if_pos h]

/-- After a rollback of an entry, the free and pending ids are those before but the entry's;
the state stays well-formed. -/
theorem rollback_ok {fl : FLPg} {txid : w64} {pd : Pending} (hwf : fl.WF)
    (h : fl.pending !! txid = some pd) (A : GMap w64 w64) :
    (∀ x, x ∈ ({ fl with pending := fl.pending.delete txid, allocs := A } : FLPg).allIds ↔
      x ∈ fl.allIds ∧ x ∉ pd.ids) ∧
    ({ fl with pending := fl.pending.delete txid, allocs := A } : FLPg).WF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hwf
  have hp := flatIds_lookup h
  have hall : fl.allIds.Perm ((fl.free ++ flatIds (fl.pending.delete txid)) ++ pd.ids) := by
    unfold FLPg.allIds
    rw [pendingIds_eq, List.append_assoc]
    exact List.Perm.append_left _ (hp.trans List.perm_append_comm)
  have hnd := hall.nodup_iff.1 h1
  have hnd' := (List.nodup_append.1 hnd)
  have hall' : ({ fl with pending := fl.pending.delete txid, allocs := A } : FLPg).allIds =
      fl.free ++ flatIds (fl.pending.delete txid) := rfl
  refine ⟨fun x => ?_, ?_, ?_, h3, ?_, ?_⟩
  · rw [hall', hall.mem_iff]
    simp only [List.mem_append]
    constructor
    · intro hx
      exact ⟨Or.inl hx, fun hm => hnd'.2.2 x (List.mem_append.2 hx) x hm rfl⟩
    · rintro ⟨hx | hx, hn⟩
      · exact hx
      · exact absurd hx hn
  · rw [hall']; exact hnd'.1
  · intro id hid; rw [hall'] at hid
    exact h2 id (hall.mem_iff.2 (List.mem_append_left _ hid))
  · rw [hall']
    have := hall.length_eq
    simp only [List.length_append] at this ⊢
    omega
  · intro t q hq
    simp only [GMap.lookup_delete_iff] at hq
    split at hq
    · cases hq
    · exact h5 t q hq

end bbolt
end EtcdGrove
end Perennial

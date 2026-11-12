/-
Lemmas of the raftLog proofs of the writing and `Ready` side (raft v3.7 retarget, stage R3).

`nextUnstable_truncateAppend_ne` is the old proof's (its `InvRaftPhys.lean`; the raft layer was
ported in stage R4), over `EntryM`; `maybeAppend` uses it.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvReadylog

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

/-- `truncateAndAppend` of a non-empty batch at or below the end of the log leaves the
batch's entries still to be handed out (`offsetInProgress` goes back to the batch's
start at most). -/
theorem nextUnstable_truncateAppend_ne [GooseExts] (ls : LogState) (ents : List EntryM)
    (e0 : EntryM) (He0 : ents[0]? = some e0)
    (Hlo : uint.Z ls.prev.index' + (ls.sents.length : Int) + 1 ≤ uint.Z ls.inprogress)
    (Hhi : uint.Z ls.inprogress ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int) + 1)
    (Hf : uint.Z ls.prev.index' < uint.Z e0.Index')
    (Hfle : uint.Z e0.Index' ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int) + 1) :
    nextUnstable (logTruncateAppend ls ents) ≠ [] := by
  obtain ⟨e0', rest, rfl⟩ : ∃ e r, ents = e :: r := by
    cases ents with
    | nil => simp at He0
    | cons e r => exact ⟨e, r, rfl⟩
  simp only [List.getElem?_cons_zero, Option.some.injEq] at He0
  subst He0
  unfold nextUnstable logOffset logTruncateAppend logTruncInprogress
  simp only [List.length_take]
  intro Hn
  have Hd : ∀ (A : List EntryM) (d : Nat), d ≤ A.length →
      (A ++ e0' :: rest).drop d ≠ [] := by
    intro A d hd h
    rw [List.drop_append_of_le_length hd] at h
    simp at h
  revert Hn
  apply Hd
  simp only [List.length_take]
  split <;> (try split) <;> omega

end EtcdGrove
end Perennial

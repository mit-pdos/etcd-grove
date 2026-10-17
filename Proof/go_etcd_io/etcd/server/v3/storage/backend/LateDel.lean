/-
The compaction's delete (etcd#21982: `UnsafeDeleteForCompaction`): bbolt's writer deletes the
entry and the pending count grows, but not `pendingDeleteOperations`, so the `Unlock` that
follows does not commit and the readers see the key until some later commit. Lean-first (no
Rocq counterpart); `notes/pr-verify/etcd-21982.md`.

In this model the readers' view (`viewOf`) agrees with the writer's contents whenever no
counted delete is pending (`sessWf`'s `ndel = 0` clause), off the hook's buckets, and a commit,
which any session or the `run` goroutine may make, must leave the clients' view (`vData`) as it
is. A delete the readers see late keeps both only in a hook's bucket (`P.HB`), whose contents
promise readers nothing: `sessWf_delC`. In any other bucket (schema's `Key`, where the PR uses
it) the readers' view would change at a commit whose committer does not hold the clients' view,
which the model excludes; that needs the backend's view to be one up to deletable keys (the
report, "What the backend's model would need").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BatchLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

/-- `UnsafeDeleteForCompaction(bucket, k)` on the buffered batch transaction: bbolt's writer
deletes the entry (no buffer), one more pending operation, and no pending delete counted. -/
def BSess.delC (st : BSess) (bi : BucketInfo) (k : GoString) : BSess :=
  { st with S := st.S.insert bi.name ((bktOf st.S bi.name).delete k),
            pend := st.pend + W64 1 }

/-- An uncounted delete keeps `sessWf` in a hook's bucket. -/
theorem sessWf_delC {P : BParams} {st : BSess} {bi : BucketInfo} {kb : GoString}
    (hP : P.Wf) (hst : sessWf P st) (hp : sint.Z st.pend + 1 < 2 ^ 58)
    (hHB : P.HB bi.name = true) :
    sessWf P (st.delC bi kb) := by
  have hSB : P.SB bi.name = false := by
    cases h : P.SB bi.name
    · rfl
    · have := hP.2.2.2.2 _ h; rw [hHB] at this; cases this
  obtain ⟨hWf, hRf, hWi, hRi, hp0, hp1, hn0, hnp, hR0, hag, hsf⟩ := hst
  have hpz : sint.Z (st.pend + W64 1) = sint.Z st.pend + 1 := by word
  refine ⟨hWf, hRf, hWi, hRi, ?_, ?_, hn0, ?_, ?_, ?_,
    safeSt_S_nonSB hsf hSB rfl rfl rfl (fun n hn => bktOf_insert_ne _ _ _ _ (Ne.symm hn))⟩
  · show 0 ≤ sint.Z (st.pend + W64 1); omega
  · show sint.Z (st.pend + W64 1) < 2 ^ 58; omega
  · show sint.Z st.ndel ≤ sint.Z (st.pend + W64 1); omega
  · intro h
    exfalso
    have : sint.Z (st.pend + W64 1) = 0 := by rw [show st.pend + W64 1 = W64 0 from h]; rfl
    omega
  · intro h n hn k
    have hne : bi.name ≠ n := fun he => by subst he; rw [hHB] at hn; cases hn
    have := hag h n hn k
    show dget (st.S.insert bi.name ((bktOf st.S bi.name).delete kb)) n k = _
    unfold dget
    rw [bktOf_insert_lookup]
    simp only [hne, ↓reduceIte]
    exact this

theorem hkData_delC {P : BParams} (st : BSess) (bi : BucketInfo) (kb : GoString)
    (h : P.hk bi.name kb = false) :
    hkData P (st.delC bi kb).S = hkData P st.S :=
  hkData_del st bi kb h

end backend
end EtcdGrove
end Perennial

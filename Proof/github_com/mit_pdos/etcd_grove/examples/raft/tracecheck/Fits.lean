/-
Lean-first (no Rocq counterpart). **The harness's receipt fits** (2026-11-12; `notes/decisions.md`,
"Trace-check's receipt bounds as instances").

`notes/bounds-plan.md` keeps the bound arithmetic out of the specs between the adequacy theorem and
the owners. The harness's specs said `receiptBound GF + 3 ≤ 2^61` (`RunConcurrent`, `Main`) and
`L.length < receiptBound GF` (`SyncRecorder.Events`', `Cluster.Events`' post); they say the two named
facts below instead, at the same strength (each is its definition):

- `tcRunFits GF`: the traced cluster's receipts fit (`receiptBound GF + 3 ≤ 2^61`): raft's receipt fit
  past the three voters' bootstrap entries (`readyFits`, `cluster_alloc`'s premise, and
  `traceReadyFits` at a traced node), which also keeps the event count below the checker's
  `numBound = 2^61` (`traceLenFits.lt_numBound`). Not a power of two, so not an instance
  (`ReceiptBoundLe GF (2^60)` would be stronger than the closed theorem's `n + 4 ≤ 2^61` gives).
- `traceLenFits GF L`: the recorder's event count is below the receipts' bound (`L.length <
  receiptBound GF`): the recorder's lock holds a time receipt per event (`recLockInv`'s `⧗ L.length`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris

section fits
variable {GF : BundledGFunctors} [ReceiptGS GF]

/-- **The traced cluster's receipts fit** (see the file header). -/
def tcRunFits (GF : BundledGFunctors) [ReceiptGS GF] : Prop :=
  receiptBound GF + 3 ≤ 2 ^ 61

/-- **The recorded events fit the receipts** (see the file header). -/
def traceLenFits {α : Type} (GF : BundledGFunctors) [ReceiptGS GF] (L : List α) : Prop :=
  L.length < receiptBound GF

/-- The fit, unfolded. -/
theorem tcRunFits.le (h : tcRunFits GF) : receiptBound GF + 3 ≤ 2 ^ 61 := h

/-- The fit, from the bound (the adequacy theorem's). -/
theorem tcRunFits.intro (h : receiptBound GF + 3 ≤ 2 ^ 61) : tcRunFits GF := h

/-- The event count's fit, from the receipts the lock holds. -/
theorem traceLenFits.intro {α : Type} {L : List α} (h : L.length < receiptBound GF) :
    traceLenFits GF L := h

/-- The event count is below any upper bound of the receipts' bound. -/
theorem traceLenFits.lt_of_le {α : Type} {L : List α} {k : Nat} (h : traceLenFits GF L)
    (hk : receiptBound GF ≤ k) : L.length < k :=
  Nat.lt_of_lt_of_le h hk

/-- **The event count is below the checker's `numBound = 2^61`** in a cluster whose receipts fit. -/
theorem traceLenFits.lt_numBound {α : Type} {L : List α} (hr : tcRunFits GF)
    (h : traceLenFits GF L) : L.length < 2 ^ 61 := by
  unfold tcRunFits at hr; unfold traceLenFits at h; omega

end fits

end TraceCheck
end EtcdGrove
end Perennial

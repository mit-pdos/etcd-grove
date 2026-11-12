/-
The committed log a write transaction makes, and the sole writer's log (pure). Until strict M1
(2026-11-05) this file also had the sole writer's resources over mvcc's internals (`soleWriter`:
the revision tokens and the certificate that pinned the logs a caller's transactions see); over
mvcc's API the pin is the caller's, in its updates (`ApiVocab.lean`, `txnBeginAU`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.Lemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace txn

open Iris Iris.BI Iris.ProofMode mvcc

/-! ## The committed log -/

/-- The state after the log a write transaction commits: the pending changes applied (none if
`pend = []`, no revision made). -/
theorem stateAfter_commitLog (ilog : Log) (pend : List Change) :
    stateAfter (commitLog ilog pend) = applyChanges (W64 ilog.length) (stateAfter ilog) pend := by
  unfold commitLog
  split
  · subst pend; rfl
  · exact stateAfter_snoc ilog pend

section sole
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]

/-- **The sole writer's log's length** (D19c's move, 2026-10-18): at least `NewStore`'s two
revisions, and a revision per non-empty change set past those two (a commit makes a revision
only of a non-empty pending one, `commitLog`), so the log's length is bounded by its changes. -/
def soleLog (log : Log) : Prop := 2 ≤ log.length ∧ log.length ≤ logCh log + 2

theorem soleLog_boot : soleLog [[], []] := by unfold soleLog logCh; simp

theorem soleLog_commit (log : Log) (pend : List Change) (h : soleLog log) :
    soleLog (commitLog log pend) := by
  unfold commitLog
  split
  · exact h
  · rename_i hp
    have : 0 < pend.length := List.length_pos_iff.2 hp
    unfold soleLog at h ⊢
    rw [logCh_snoc]; simp only [List.length_append, List.length_singleton]; omega

end sole

end txn
end EtcdGrove
end Perennial

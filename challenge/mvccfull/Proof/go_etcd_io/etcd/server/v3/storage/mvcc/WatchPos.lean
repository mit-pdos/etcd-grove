/-
**A log's watch events are positive** (pure; stage 2 of the mvcc API proof, the watch chain:
`notes/mvcc-api-invariants.md`, "Hand-off: stage 2, exactness per watcher", (e); 2026-11-05).
Lean-first (no Rocq counterpart).

`wsRecvOk`'s first conjunct asks of every event received a positive revision and, for a put, a
positive creation revision and version (`respShape`'s last conjunct, `Api/SentInv.lean`). They are
true of every event of a log whose revision `0` is empty, with fewer than `2 ^ 63` revisions and
fewer than `2 ^ 63 - 1` changes (a version counts a key's puts, so is at most the changes):
`logEvents_pos`, and `watchEvents_pos`, `filtered_pos` of its sub-lists. A sealed log has them
(`idxSealed`: `LogWf'`, its length, its receipt `⧖ (logCh log)` below the receipts' bound, which a
store's invariant bounds by `2 ^ 48`). A doomed watcher's events are a sub-list of such a log's
(`syncWatchers`' scan), so the same lemma serves for them.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris go_etcd_io.etcd.server.v3.storage.mvcc

variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **An event is positive**: its revision, and a put's creation revision and version
(`respShape`'s last conjunct). -/
def evPos (ev : EvM) : Prop :=
  0 < sint.Z ev.kv.modRev ∧ (ev.del = false → 0 < sint.Z ev.kv.createRev ∧ 0 < sint.Z ev.kv.version)

end mvcc
end EtcdGrove
end Perennial

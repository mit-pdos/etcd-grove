/-
`store.Compact` (`kvstore.go`): compaction (2026-10-13, unit 5a; `notes/decisions.md`, "mvcc: compaction").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`s.Compact(trace, rev)`** with the compaction right at the store's compaction revision `c`
(`compactRightR`: half the revision's authority and the compaction jobs' queue on the store's FIFO
scheduler, 2026-10-13, unit 5c; restorable since M2, the storage side, item 17: the closer's half
and the jobs' leased share of the fields kept, not discarded, so `store.Close` takes it back; the caller is the one that compacts: the server's apply thread,
and the exclusive right serializes its compactions: the job is scheduled after `s.mu` is
released, so only the right can carry the queue there), under the critical-section
contract of the batch lock (`csContract`: `SetScheduledCompact`'s `LockInsideApply` runs the
post-lock hook), `trace ≠ nil`, the store's backend supporting the compaction (`storeCmp`: mvcc's
assumed backend, or a real backend in compaction mode, `KBReal.cm`: question 5's core stage, part
(4), 2026-10-29; until then the assumed backend only); under `s.mu` held exclusively (no transaction open):
* `rev > c`, `rev` a revision of the committed log: the compaction revision is `rev` (the right
  at `rev`, its queue ending with the job's `Post`, a lower bound `crevLb γ rev` for every reader
  since), `nil`, the caller's `Post`, and the job's channel (`compactChan`: once closed, `compactDone s γ rev`: the index and the bucket
  compacted at `rev`, `finishedCompactRev = rev`, or the compaction interrupted by `Close`);
* `rev ≤ c`: `ErrCompacted`, the barrier's channel (closed once the jobs before it ran:
  nothing promised, `True`), `Pre` back.
The code's third case, `rev` above the committed log's last revision (`ErrFutureRev`), does not
arise: the caller's certificate (below) is of a prefix of the committed log (M2, the apply side,
item 18, 2026-10-30; until then a third arm, with a certificate of a shorter log).
The right's revision is at least `-1` (`NewStore`'s; each success raises it: 2026-10-13, unit 5c,
contract correction: the counter `crevN` cannot tell a right below `-1` from one at `-1`, and
then a `rev` in `(c, -1]` is `ErrCompacted` without `rev ≤ c`). The configuration's batch limit
is positive (`isStore`: `NewStore` excludes a negative one,
`issues/etcd-compaction-negative-batch-limit.md`).

**The delete-then-put premise** (2026-10-13, unit 6a): the caller holds a certificate of a log
`log` with revision `rev` (so `rev` is not above the committed log) whose revision `rev` does not delete a key and put it again
(`NoDelPutAt`): else the compaction deletes the key's live value and a later read `Fatal`s
(`issues/etcd-compaction-delete-then-put.md`). The store records it for the new compaction
revision (`crevSafe`, in `s.mu`'s resource) and the keys the job deletes carry it (`delKey`), which
is what makes the readers' specs hold of a compacted store (`rangeAnswers_not_del`).

**The physical bound** (item 8, 2026-10-17; not a premise since 2026-10-18, D19b): the log up to
`rev` has fewer than `2 ^ 62` changes (`CompactSmall`), so the job's count of deleted keys (an
`int`) never wraps and `dbCompactionKeysCounter.Add(float64(count))` gets a non-negative value;
the job derives it from the certificate's time-receipt bound (`CompactSmall_of_cert`).

**The reader's token** (question 5's switch, decision (i), 2026-10-29): the caller lends the store's
reader token `storeRT γ` (the apply thread's, from `writerOwn`) for `checkPrevCompactionCompleted`'s
`ReadTx`, and gets it back in every case.

**The writer's hook** (Probe P1, 2026-10-30): `hookIs γ P f` (the persistent `hookOk` and the
writer's fragment `writerFrag`) is given back in every case, so the caller can still write
(`store.Write`), compact again, or restore.

**The write-back supply** (M2, the storage side, Q1 (a), 2026-10-30): the caller gives the
compaction's supply `kbWTSupplyM γ.kb` (persistent; the server's from its write budget, R2-7),
which the store no longer keeps; the job gets it in its premise (`compactJobPre`).
-/
abbrev mvcc.store.Compact.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (rev : w64) (c : Int) (P : IProp GF) (f : val)
    (Pre Q Post : IProp GF) (log : mvcc.Log) (te : Bool),
  trace ≠ null → mvcc.storeCmp γ → -1 ≤ c →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.compactRightR s γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝ ∗
      mvcc.hookIs γ P f ∗
      mvcc.csContract P f Pre Q Post ∗ traceutil.ownTrace trace te ∗ mvcc.storeRT γ ∗
      mvcc.kbWTSupplyM γ.kb }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Compact")) (Val #trace)) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); traceutil.ownTrace trace te ∗ mvcc.storeRT γ ∗ mvcc.hookIs γ P f ∗
      ((⌜err = GoInterface.nil ∧ c < sint.Z rev⌝ ∗ mvcc.compactRightR s γ (sint.Z rev) ∗
        mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗ mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev))) ∨
      (⌜sint.Z rev ≤ c⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.compactRightR s γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True))) }}

end spec

end EtcdGrove
end Perennial

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **`s.Compact(trace, rev)`** with the compaction right at the store's compaction revision `c`
(`compactRight`: half the revision's authority and the compaction jobs' queue on the store's FIFO
scheduler, 2026-10-13, unit 5c; the caller is the one that compacts: the server's apply thread,
and the exclusive right serializes its compactions: the job is scheduled after `s.mu` is
released, so only the right can carry the queue there), under the critical-section
contract of the batch lock (`csContract`: `SetScheduledCompact`'s `LockInsideApply` runs the
post-lock hook), `trace ≠ nil`, the store's backend supporting the compaction (`storeCmp`: mvcc's
assumed backend; 2026-10-13, the merge with the real backend, whose model has no deletion from
the `Key` bucket); under `s.mu` held exclusively (no transaction open):
* `rev > c`, `rev` a revision of the committed log: the compaction revision is `rev` (the right
  at `rev`, its queue ending with the job's `Post`, a lower bound `crevLb γ rev` for every reader
  since), `nil`, the caller's `Post`, and the job's channel (`compactChan`: once closed, `compactDone s γ rev`: the index and the bucket
  compacted at `rev`, `finishedCompactRev = rev`, or the compaction interrupted by `Close`);
* `rev ≤ c`: `ErrCompacted`, the barrier's channel (closed once the jobs before it ran:
  nothing promised, `True`), `Pre` back;
* `rev` above the committed log's last revision (a certificate of a shorter log): `ErrFutureRev`,
  a `nil` channel, `Pre` back.
The right's revision is at least `-1` (`NewStore`'s; each success raises it: 2026-10-13, unit 5c,
contract correction: the counter `crevN` cannot tell a right below `-1` from one at `-1`, and
then a `rev` in `(c, -1]` is `ErrCompacted` without `rev ≤ c`). The configuration's batch limit
is positive (`isStore`: `NewStore` excludes a negative one,
`issues/etcd-compaction-negative-batch-limit.md`).

**The delete-then-put premise** (2026-10-13, unit 6a): the caller holds a certificate of a log
`log` with revision `rev` (so `rev` is not above the committed log: the `ErrFutureRev` case does
not arise from such a caller) whose revision `rev` does not delete a key and put it again
(`NoDelPutAt`): else the compaction deletes the key's live value and a later read `Fatal`s
(`issues/etcd-compaction-delete-then-put.md`). The store records it for the new compaction
revision (`crevSafe`, in `s.mu`'s resource) and the keys the job deletes carry it (`delKey`), which
is what makes the readers' specs hold of a compacted store (`rangeAnswers_not_del`). -/
abbrev mvcc.store.Compact.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (rev : w64) (c : Int) (P : IProp GF) (f : val)
    (Pre Q Post : IProp GF) (log : mvcc.Log),
  trace ≠ null → mvcc.storeCmp γ → -1 ≤ c →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeStop s ∗ mvcc.compactRight γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝ ∗
      mvcc.hookIs γ P f ∗
      mvcc.csContract P f Pre Q Post }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Compact")) (Val #trace)) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err);
      (⌜err = GoInterface.nil ∧ c < sint.Z rev⌝ ∗ mvcc.compactRight γ (sint.Z rev) ∗
        mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗ mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev))) ∨
      (⌜sint.Z rev ≤ c⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.compactRight γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True)) ∨
      (⌜c < sint.Z rev ∧ ch = chan.nil⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        (∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ ⌜(log.length : Int) ≤ sint.Z rev⌝) ∗
        mvcc.compactRight γ c ∗ Pre) }}

end spec

end EtcdGrove
end Perennial

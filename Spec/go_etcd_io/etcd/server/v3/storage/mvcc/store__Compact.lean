/-
`store.Compact` (`kvstore.go`): compaction (2026-10-13, unit 5a; `notes/decisions.md`, "mvcc: compaction").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LockArm

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
and the jobs' leased share of the fields kept, not discarded, so `store.Close` takes it back; the
caller is the one that compacts, and the exclusive right serializes its compactions: the job is
scheduled after `s.mu` is released, so only the right can carry the queue there), under the
critical section's context by the post-lock hook's state (`lockCtxM`: `SetScheduledCompact`'s
`LockInsideApply` runs the hook, or nothing), `trace ≠ nil`, the store's backend supporting the
compaction (`storeCmp`), a revision past `0`, and the caller's ghost step `cmpCb` with its excluder
`S` (`updateCompactRev`'s, `KV.Compact.contract`, 2026-11-06); under `s.mu` held exclusively (no
transaction open):
* `rev > c`, `rev` a revision of the committed log: the compaction revision is `rev` (the right
  at `rev`, its queue ending with the job's `Post`, a lower bound `crevLb γ rev` for every reader
  since), `nil`, the caller's `Post`, `Fok`, and the job's channel (`compactChan`: once closed,
  `compactDone s γ rev`: the index and the bucket compacted at `rev`, `finishedCompactRev = rev`, or
  the compaction interrupted by `Close`);
* `rev ≤ c`: `ErrCompacted`, the barrier's channel (closed once the jobs before it ran: nothing
  promised, `True`), `Pre` back, `Fce`;
* `rev` above the committed log's last revision: `ErrFutureRev`, no channel, `Pre` back, `Ffr`
  (`KV.Compact.contract`, 2026-11-06: until then excluded by the caller's certificate of a log with
  revision `rev`).
The right's revision is at least `-1` (`NewStore`'s; each success raises it: 2026-10-13, unit 5c,
contract correction). The configuration's batch limit is positive (`isStore`: `NewStore` excludes a
negative one, `nonissues/etcd-compaction-negative-batch-limit.md`).

**The physical bound** (item 8, 2026-10-17; not a premise since 2026-10-18, D19b): the job derives
it from the committed log's time-receipt bound (`CompactSmall_of_cert`).

**The reader's token** (question 5's switch, decision (i), 2026-10-29): the caller lends the store's
reader token `storeRT γ` for `checkPrevCompactionCompleted`'s `ReadTx`, and gets it back in every
case. **The hook's context** (`lockBackM`) is given back in every case. **The write-back supply**
(M2, the storage side, Q1 (a), 2026-10-30): the caller gives the compaction's supply
`kbWTSupplyM γ.kb` (persistent), which the job gets in its premise (`compactJobPre`). The revision
is permitted (`crevPermAt`, C3's store law, 2026-11-02).

(Internal: the canonical `store.Compact.spec` is to be `KV.Compact.contract` at `*store`, of which
this is the core.) -/
abbrev mvcc.store.Compact.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (trace : Loc) (rev : w64) (c : Int) (P : IProp GF)
    (hk : Option val) (Pre Q Post S Fok Fce Ffr : IProp GF) (te : Bool),
  trace ≠ null → mvcc.storeCmp γ → -1 ≤ c → 1 ≤ sint.Z rev →
  (mvcc.slotF γ ∗ S ⊢ False) → (ghostVar γ.wr 1 () ∗ mvcc.slotFr γ ∗ S ⊢ False) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.compactRightR s γ c ∗
      mvcc.crevPermAt γ (sint.Z rev) ∗ mvcc.lockCtxM γ P hk Pre Q Post ∗
      traceutil.ownTrace trace te ∗ mvcc.storeRT γ ∗ mvcc.kbWTSupplyM γ.kb ∗ S ∗
      mvcc.cmpCb γ c c (sint.Z rev) Fok Fce Ffr }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Compact")) (Val #trace)) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); traceutil.ownTrace trace te ∗
      mvcc.storeRT γ ∗ mvcc.lockBackM γ P hk ∗ S ∗
      ((⌜err = GoInterface.nil ∧ c < sint.Z rev⌝ ∗ mvcc.compactRightR s γ (sint.Z rev) ∗
        mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗ mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev)) ∗
        Fok) ∨
      (⌜sint.Z rev ≤ c⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.compactRightR s γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True) ∗ Fce) ∨
      (⌜ch = chan.nil⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        mvcc.compactRightR s γ c ∗ Pre ∗ Ffr)) }}

end spec

end EtcdGrove
end Perennial

/-
`store.compactLockfree` (`kvstore.go`) (2026-10-13, unit 5a).
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

/-- `s.compactLockfree(rev)` (`restore`'s, with `s.mu` held exclusively: `muInvAt s γ 1 c`):
`updateCompactRev` then, on success, `compact` (at `context.TODO()`'s trace), the job scheduled on
the compaction right's queue (2026-10-13, unit 5c); not `ErrFutureRev`, which the caller's
certificate excludes (M2, the apply side, item 18, 2026-10-30). Of a store whose
backend supports the compaction (`storeCmp`). The caller holds a certificate of a log with
revision `rev`, as `store.Compact`'s (no `NoDelPutAt` since M2's item 18).

**The reader's token** (question 5's switch, decision (i), 2026-10-29): the caller lends the store's
reader token `storeRT γ` (the apply thread's, from `writerOwn`) for `checkPrevCompactionCompleted`'s
`ReadTx`, and gets it back in every case. So is the caller's hook context (`lockCtxM`/`lockBackM`,
by the hook's state: `restore()` resumes a compaction with it unset; item 31, 2026-10-30; until
then `hookIs γ P f` with `csContract`, Probe P1, 2026-10-30). 
The revision is permitted (`crevPermAt`, C3's store law, 2026-11-02): the store's compaction
permit holds of it, which `s.mu`'s and `s.revMu`'s resources keep of the compaction revision.

**The lag** (M2's item 15, 2026-11-02), as `updateCompactRev`'s: `compactMainRev` may hold `cp`,
below `c` (`muInvLag`), when `rev` is at least `c` (`restore()`'s resumed compaction); the
success case ends it, with the lag's token back (`lagTok`).

**The scope restriction** (F2, stage 2; the user's Q7, approved 2026-11-03): the revision is at least
`1`, no compaction at revision `0` (`nonissues/etcd-restore-scheduled-compact-zero.md`: a member that
compacted at `0` and restores mid-way through that compaction goes back to compaction revision `-1`).
In compaction mode the backend's tracking records the compaction's records as positive revisions
(`physCut`'s `recsPos`); etcd does not enforce it. The caller, `restore()`'s resumed compaction,
has it of the image's scheduled record (`recsPos`), past Go's own resume guard
(`kvstore.go:389`, `scheduledCompact != 0`: a scheduled record of `0` is never resumed).

**The tracking** (F2, stage 2), as `updateCompactRev`'s: the whole of `s.mu`'s deposit ghost
(`γ.wr`), lent to it and given back. -/
abbrev mvcc.store.compactLockfree.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev : w64) (c cp : Int) (P : IProp GF) (hk : Option val)
    (Pre Q Post : IProp GF) (log : mvcc.Log),
  mvcc.storeCmp γ → 1 ≤ sint.Z rev → (cp < c → c ≤ sint.Z rev) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.muInvLag s γ c cp ∗ mvcc.compactRightR s γ c ∗
      mvcc.crevPermAt γ (sint.Z rev) ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length⌝ ∗
      mvcc.lockCtxM γ P hk Pre Q Post ∗ mvcc.storeRT γ ∗ mvcc.kbWTSupplyM γ.kb ∗
      ghostVar γ.wr 1 () }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compactLockfree")) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); mvcc.storeRT γ ∗ mvcc.lockBackM γ P hk ∗
      ghostVar γ.wr 1 () ∗
      ((⌜err = GoInterface.nil ∧ cp < sint.Z rev ∧ c ≤ sint.Z rev⌝ ∗ mvcc.muInvAt s γ 1 (sint.Z rev) ∗
        mvcc.compactRightR s γ (sint.Z rev) ∗ mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗
        mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev)) ∗ mvcc.lagTok γ c cp) ∨
      (⌜sint.Z rev ≤ c ∧ cp = c⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True))) }}

end spec

end EtcdGrove
end Perennial

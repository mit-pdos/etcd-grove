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
then `hookIs γ P f` with `csContract`, Probe P1, 2026-10-30). -/
abbrev mvcc.store.compactLockfree.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev : w64) (c : Int) (P : IProp GF) (hk : Option val)
    (Pre Q Post : IProp GF) (log : mvcc.Log),
  mvcc.storeCmp γ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length⌝ ∗
      mvcc.lockCtxM γ P hk Pre Q Post ∗ mvcc.storeRT γ ∗ mvcc.kbWTSupplyM γ.kb }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compactLockfree")) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err); mvcc.storeRT γ ∗ mvcc.lockBackM γ P hk ∗
      ((⌜err = GoInterface.nil ∧ c < sint.Z rev⌝ ∗ mvcc.muInvAt s γ 1 (sint.Z rev) ∗
        mvcc.compactRightR s γ (sint.Z rev) ∗ mvcc.crevLb γ.idx (sint.Z rev) ∗ Post ∗
        mvcc.compactChan ch (mvcc.compactDone s γ (sint.Z rev))) ∨
      (⌜sint.Z rev ≤ c⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True))) }}

end spec

end EtcdGrove
end Perennial

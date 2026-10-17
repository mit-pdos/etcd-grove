/-
`store.updateCompactRev` (`kvstore.go`): the compaction revision updated (2026-10-13, unit 5a; `InvStore.lean`).
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

/-- `s.updateCompactRev(rev)`, with `s.mu` held exclusively (`muInvAt s γ 1 c`: its part of
`compactMainRev` and of the revision's authority, at the compaction revision `c`) and the
compaction right at `c`, the store's backend supporting the compaction (`storeCmp`), under the
critical-section contract of the batch lock (`csContract`:
`SetScheduledCompact`'s `LockInsideApply` runs the post-lock hook):
* `rev > c`, `rev` a revision of the committed log: under `s.revMu`, `compactMainRev = rev` (both
  locks' halves, the authority with the right's), `scheduledCompactRev = rev` written, `nil`, the
  previous compaction revision; the right at `rev` (its queue unchanged, good at `rev`:
`compactQueue_mono`); the job's premises (`compactJobPre`: `crevLb γ rev`, the caller's
  certified log with revision `rev`, which does not delete then put a key) and the caller's
  `Post`; `s.mu`'s resource records the revision safe for readers (`crevSafe`; 2026-10-13, unit
  6a: the caller's `NoDelPutAt`, as `store.Compact`'s);
* `rev ≤ c`: `ErrCompacted`, and a barrier job scheduled that closes the channel returned (a
  receive right, `compactChan ch True`); nothing changed, `Pre` back;
* `rev` above the committed log's last revision: `ErrFutureRev`, a `nil` channel; `Pre` back.

**etcd-io/etcd#21968** (`pr-verify/etcd-21968`): the result has a third component, the store's
`currentRev` read under `s.revMu` (`cur`), and the error cases return the compaction revision `c`
as `prev` (was `0`). In every case `cur` is the last revision of the committed log at the time
(a certificate `logh` with `cur = |logh| - 1`): on success `rev ≤ cur`; on `ErrCompacted`
`c ≤ cur` (the store's compaction revision is never above its head: `revMuInv`'s `Hc`) and the
caller's certified log is a prefix of `logh` (so `cur = rev` means the caller's log ends at
`rev = c`); on `ErrFutureRev` `cur < rev`. -/
abbrev mvcc.store.updateCompactRev.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev : w64) (c : Int) (P : IProp GF) (f : val)
    (Pre Q Post : IProp GF) (log : mvcc.Log),
  mvcc.storeCmp γ →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeStop s ∗ mvcc.muInvAt s γ 1 c ∗ mvcc.compactRight γ c ∗
      mvcc.idxCert γ.idx log ∗ ⌜sint.Z rev < log.length ∧ mvcc.NoDelPutAt log (sint.Z rev)⌝ ∗
      mvcc.hookIs γ P f ∗ mvcc.csContract P f Pre Q Post }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"updateCompactRev")) (Val #rev))
  {{ (ch : GoChan) (prev : w64) (cur : w64) (err : GoInterface),
      RET (PairV (PairV (PairV #ch #prev) #cur) #err);
      (⌜err = GoInterface.nil ∧ ch = chan.nil ∧ prev = W64 c ∧ c < sint.Z rev ∧
          sint.Z rev ≤ sint.Z cur⌝ ∗
        mvcc.muInvAt s γ 1 (sint.Z rev) ∗ mvcc.compactRight γ (sint.Z rev) ∗ Post ∗
        mvcc.compactJobPre s γ rev) ∨
      (⌜sint.Z rev ≤ c ∧ prev = W64 c ∧ c ≤ sint.Z cur⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        (∃ logh : mvcc.Log, mvcc.idxCert γ.idx logh ∗
          ⌜sint.Z cur = (logh.length : Int) - 1 ∧ log.length ≤ logh.length⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRight γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True)) ∨
      (⌜c < sint.Z rev ∧ ch = chan.nil ∧ prev = W64 c⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        (∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗
          ⌜(log.length : Int) ≤ sint.Z rev ∧ sint.Z cur = (log.length : Int) - 1⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRight γ c ∗ Pre) }}

end spec

end EtcdGrove
end Perennial

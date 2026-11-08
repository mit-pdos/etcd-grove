/-
`store.updateCompactRev` (`kvstore.go`): the compaction revision updated (2026-10-13, unit 5a; `InvStore.lean`).
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

/-- `s.updateCompactRev(rev)`, with `s.mu` held exclusively (`muInvLag s γ c cp`: its part of
`compactMainRev` and of the revision's authority, at the compaction revision `c`) and the
compaction right at `c` (`compactRightR`: restorable, the closer kept; M2, the storage side,
item 17), the store's backend supporting the compaction (`storeCmp`), under the critical
section's context by the post-lock hook's state (`lockCtxM`; M2, the storage side, item 31,
2026-10-30): set to `f`, the critical-section contract of the batch lock (`csContract`:
`SetScheduledCompact`'s `LockInsideApply` runs the hook); unset (`hk = none`: `restore()`'s
resumed compaction, inside `kv.Restore`, before the server sets the new backend's hook), the
unset hook lent and the caller's update from `P ∗ Pre` to `P ∗ Post` (`LockInsideApply` runs
nothing), at any share `dq` of the hook at `nil` (§4.8, 2026-11-06: the frozen one of a store
without a hook). **The caller's ghost step** (`cmpCb`; `KV.Compact.contract`, 2026-11-06: until then the
placeholders `rcvSched_M1`, `slotX_step_M1` and `regLent_excl_M1` moved the API's ghost state with
no client) is fired at the code's three outcomes, and the caller's excluder `S` (lent, given back)
keeps the writer's invariant out of its frozen and restoring states (`hS1`, `hS2`) while the
success's step fires inside `SetScheduledCompact`'s loan:
* `cp < rev ≤ currentRev`: under `s.revMu`, `compactMainRev = rev` (both locks' halves, the
  authority with the right's), `scheduledCompactRev = rev` written, `nil`, the previous compaction
  revision, `cmpCb`'s `Fok`; the right at `rev` (its queue unchanged, good at `rev`:
  `compactQueue_mono`); the job's premises (`compactJobPre`: `crevLb γ rev`, the committed log
  with revision `rev`) and the caller's `Post`; `s.mu`'s resource records the revision's
  certificate (`crevSafe`, the committed log's);
* `rev ≤ cp`: `ErrCompacted`, and a barrier job scheduled that closes the channel returned (a
  receive right, `compactChan ch True`), tracked (M2, the storage side, item 17: the right's queue,
  the last job's `Post` passed through); nothing changed, `Pre` back, `Fce`;
The success's `ForceCommit` serves the caller's commit request (`storeReq γ X Y`, its `X` to `Y`;
`KV.Compact.contract`'s backend commit, 2026-11-06: until then at `True`); the error arms give `X`
back.
* `rev > currentRev` (`ErrFutureRev`; `KV.Compact.contract`, 2026-11-06: until then excluded by the
  caller's certificate of a log with revision `rev`): `nil`, nothing changed, `Pre` back, `Ffr`.

The store's reader token `storeRT γ` is lent and given back in every case (question 5's core stage,
parts (2)-(4), decided by the agent: `SetScheduledCompact`'s `LockInsideApply` and the
`ForceCommit` after it take it; the caller's, `compactLockfree`'s and `store.Compact`'s). Their
write-back tokens come from the caller's supply (`kbWTSupplyM`, M2's Q1 (a)) and the receipts of its own
steps. The caller's hook context (`lockBackM`: the hook's facts `hookOk γ P f`, or the unset hook) is
given back in every case (Probe P1, 2026-10-30).
The revision is permitted (`crevPermAt`, C3's store law, 2026-11-02): the store's compaction
permit holds of it, which `s.mu`'s and `s.revMu`'s resources keep of the compaction revision.
The revision is past `0` (`KV.Compact.contract`'s premise; the resumed compaction's, the records'
`recsPos`).

**The lag** (M2's item 15, 2026-11-02): `compactMainRev` may hold `cp`, below `c` (`muInvLag`;
`muInvAt s γ 1 c` is `cp = c`, `muInvLag_at`): `restore()`'s resumed compaction, after `restore()`
stored the finished record, at a revision `rev` at least `c`; the success case's then, with the
lag's token back (`lagTok`), the error cases' not. -/
abbrev mvcc.store.updateCompactRev.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev : w64) (c cp : Int) (P : IProp GF) (hk : Option val)
    (dq : DFrac) (Pre Q Post S Fok Fce Ffr X Y : IProp GF),
  mvcc.storeCmp γ → (cp < c → c ≤ sint.Z rev) → 1 ≤ sint.Z rev →
  (mvcc.slotF γ ∗ S ⊢ False) → (ghostVar γ.wr 1 () ∗ mvcc.slotFr γ ∗ S ⊢ False) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.muInvLag s γ c cp ∗ mvcc.compactRightR s γ c ∗
      mvcc.crevPermAt γ (sint.Z rev) ∗
      mvcc.lockCtxM γ P hk Pre Q Post dq ∗ mvcc.storeRT γ ∗ mvcc.kbWTSupplyM γ.kb ∗ S ∗
      mvcc.cmpCb γ c cp (sint.Z rev) Fok Fce Ffr ∗ X ∗ mvcc.storeReq γ X Y }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"updateCompactRev")) (Val #rev))
  {{ (ch : GoChan) (prev : w64) (err : GoInterface), RET (PairV (PairV #ch #prev) #err);
      mvcc.storeRT γ ∗ mvcc.lockBackM γ P hk dq ∗ S ∗
      ((⌜err = GoInterface.nil ∧ ch = chan.nil ∧ prev = W64 cp ∧ cp < sint.Z rev ∧ c ≤ sint.Z rev⌝ ∗
        mvcc.muInvAt s γ 1 (sint.Z rev) ∗ mvcc.compactRightR s γ (sint.Z rev) ∗ Post ∗
        mvcc.compactJobPre s γ rev ∗ mvcc.lagTok γ c cp ∗ Fok ∗ Y) ∨
      (⌜sint.Z rev ≤ c ∧ cp = c ∧ prev = W64 0⌝ ∗
        (∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗ ⌜err = GoInterface.ok ec⌝) ∗
        mvcc.muInvAt s γ 1 c ∗ mvcc.compactRightR s γ c ∗ Pre ∗ mvcc.compactChan ch iprop(True) ∗ Fce ∗
        X) ∨
      (⌜ch = chan.nil ∧ prev = W64 0⌝ ∗
        (∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗ ⌜err = GoInterface.ok ef⌝) ∗
        mvcc.muInvLag s γ c cp ∗ mvcc.compactRightR s γ c ∗ Pre ∗ Ffr ∗ X)) }}

end spec

end EtcdGrove
end Perennial

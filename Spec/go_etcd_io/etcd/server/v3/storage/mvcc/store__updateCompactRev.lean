/-
`(*store).updateCompactRev(rev)` (`kvstore.go:197`). Internal: `Compact` (under `s.mu`) and
`compactLockfree` (`restore`'s resumed compaction, under `s.mu`).

**Proof sketch**: under `s.revMu` (`revsAt`, the caller's update fired there): at or below the
compaction revision, a barrier job scheduled (the scheduler's share in `s.mu`'s resources,
`storeWB`) and `ErrCompacted`; past the current revision, `ErrFutureRev`; else `compactMainRev :=
rev`, `SetScheduledCompact` (the storage's hook under its batch lock, `Pre` to `Q'`, `Pk` back to
`Unlock`; the scheduled key written through the store's storage-data protocol in `storeWB`), the
forced commit (`X` to `Y`), and the job's resources (`compactJobRes`) for `compact`.

**Changes** from `specs-ref`'s file: over `storeWB`/`revsAt` and the storage contract
(`storageHook`, `hookRun`, `storageReq`) in place of `muInvLag`, `compactRightR`, `lockCtxM`,
`cmpCb`; the hook at any share (`Restore`'s and `NewStore`'s unset hook, `Compact`'s frozen one).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.updateCompactRev(rev)` (`rev ≥ 1`, `s.mu` held): by the caller's update at the store's
revisions `(cur, c)`: a compaction at `rev` when `c < rev ≤ cur` (the hook run, the scheduled key
written and committed, the job's resources); `ErrCompacted` and a barrier's channel at or below
`c`; `ErrFutureRev` and no channel past `cur`. -/
def store.updateCompactRev.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (rev : w64) (B : MvccStorage) (Pk : IProp GF) (dq : DFrac)
    (f : GoFunc) (Pre Q' Post X Y : IProp GF) (Φ : Nat → Int → IProp GF),
  let ok (cur : Nat) (c : Int) : Prop := c < sint.Z rev ∧ sint.Z rev ≤ (cur : Int)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ isStore s γ ∗
      storeWB s γ B Pk ∗ ⌜1 ≤ sint.Z rev⌝ ∗ storageHook B dq f ∗ Pre ∗ hookRun Pk f Pre Q' ∗
      (Q' ={⊤}=∗ Pk ∗ Post) ∗ X ∗ storageReq B Pk X Y ∗ schemaVars ∗
      AU <{ ∃∃ (cur : Nat) (c : Int), revsAt γ cur c }> @ ⊤ \ ↑mvccN, ∅
        <{ revsAt γ cur (if ok cur c then sint.Z rev else c), COMM Φ cur c }> }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"updateCompactRev")) (Val #rev))
  {{ (ch : GoChan) (prev : w64) (err : GoInterface), RET (PairV (PairV #ch #prev) #err);
      storeWB s γ B Pk ∗ storageHook B dq f ∗ ∃ (cur : Nat) (c : Int), Φ cur c ∗
      ((⌜ok cur c ∧ err = GoInterface.nil ∧ ch = chan.nil ∧ prev = W64 c⌝ ∗ Post ∗ Y ∗
          compactJobRes s γ rev prev) ∨
       (⌜sint.Z rev ≤ c ∧ prev = W64 0⌝ ∗ globalAddr ErrCompacted ↦□ err ∗ Pre ∗ X ∗
          compactChanOk ch) ∨
       (⌜(cur : Int) < sint.Z rev ∧ ch = chan.nil ∧ prev = W64 0⌝ ∗ globalAddr ErrFutureRev ↦□ err ∗
          Pre ∗ X)) }}

end spec
end Mvcc
end EtcdGrove
end Perennial

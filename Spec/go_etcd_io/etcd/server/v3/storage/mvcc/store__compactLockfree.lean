/-
`(*store).compactLockfree(rev)` (`kvstore.go:262`). Internal: `restore`, resuming a compaction the
image scheduled and did not finish (under `s.mu`).

**Proof sketch**: `checkPrevCompactionCompleted` (a reader slot), `updateCompactRev` (the caller's
update over `revsAt`, the hook, the commit), then on success `compact` with a fresh trace
(`traceutil.TODO()`, 4b's).

**Changes** from `specs-ref`'s file: over `InternalStore.lean`, the hook at any share.
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

/-- `s.compactLockfree(rev)` (`rev ≥ 1`, `s.mu` held): `updateCompactRev`'s outcome, the job
scheduled on success. -/
def store.compactLockfree.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (rev : w64) (B : MvccStorage) (Pk : IProp GF) (dq : DFrac)
    (f : GoFunc) (Pre Q' Post X Y : IProp GF) (Φ : Nat → Int → IProp GF),
  let ok (cur : Nat) (c : Int) : Prop := c < sint.Z rev ∧ sint.Z rev ≤ (cur : Int)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ isStore s γ ∗
      storeWB s γ B Pk ∗ schedRight s γ ∗ kbRdToks B 1 ∗ ⌜1 ≤ sint.Z rev⌝ ∗ storageHook B dq f ∗
      Pre ∗ hookRun Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗ X ∗ storageReq B Pk X Y ∗ schemaVars ∗
      AU <{ ∃∃ (cur : Nat) (c : Int), revsAt γ cur c }> @ ⊤ \ ↑mvccN, ∅
        <{ revsAt γ cur (if ok cur c then sint.Z rev else c), COMM Φ cur c }> }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"compactLockfree")) (Val #rev))
  {{ (ch : GoChan) (err : GoInterface), RET (PairV #ch #err);
      storeWB s γ B Pk ∗ schedRight s γ ∗ kbRdToks B 1 ∗ storageHook B dq f ∗
      ∃ (cur : Nat) (c : Int), Φ cur c ∗
      ((⌜ok cur c ∧ err = GoInterface.nil⌝ ∗ Post ∗ Y ∗ compactChanOk ch) ∨
       (⌜sint.Z rev ≤ c⌝ ∗ globalAddr ErrCompacted ↦□ err ∗ Pre ∗ X ∗ compactChanOk ch) ∨
       (⌜(cur : Int) < sint.Z rev ∧ ch = chan.nil⌝ ∗ globalAddr ErrFutureRev ↦□ err ∗ Pre ∗ X)) }}

end spec
end Mvcc
end EtcdGrove
end Perennial

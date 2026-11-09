/-
`(*store).restore()` (`kvstore.go:317`). Internal: `NewStore` and `Restore` (under `s.mu`, with a
fresh index, scheduler and stop channel), over a storage holding an image of any history `h`.

**Proof sketch**: `setupMetricsReporter`; `ReadTx`, `RLock` (a reader slot of `mvccStorageFor`'s;
the snapshot `kbRead` and the whole liveness `kbLive B rt 1`);
`UnsafeReadFinishedCompact` (the image's finished compaction: `compactMainRev`) and
`UnsafeReadScheduledCompact` (each lent a share of the liveness, back at once); `restoreIntoIndex`
over the image's `Key` entries in order (`RestoreEntsOk`: the image's keys parse, its values
decode); `UnsafeRange` chunks of `restoreChunkKeys` (the shared read transaction's `rtRange`: exact
cuts, the image `clean`, `mvccStorageFor`), each lent against a new share of the liveness (half of
what is left: `rangeLent`), `restoreChunk` each with half of the chunk's lent fraction (the values
back; the keys lent on to the index goroutine, `rkvProducer`'s loans), the next chunk's start after
the last key (read with the other half; `BytesToRev` parses it); `close(rkvc)` (`rkvClose`); `<-revc`
(`revRecv`: the index rebuilt, `idxRestore`, published, `idxShareC`, and the keys' loans back, so
every chunk's wand gives its liveness share back: `kbLive B rt 1` again for `RUnlock`); `currentRev` at least the compaction revisions (so `h.rev`:
an image's last revision is its history's, a compacted tail or a deleted tombstone at the scheduled
compaction being why the Go code raises it); the leases re-attached through `le.Attach` (the store's lessor a real `*lessor`, `Lease.isLessor`:
the `panic("no lessor to attach lease")` unreachable; each `Attach` steps the writer's token,
`lessor.Attach.spec`; one failing for a lease the lessor lacks is logged: `RestoreLs`, any map
order); `RUnlock`; with an unfinished compaction (`u`: the scheduled key
above the finished one, so `h.compacted` the scheduled one) `compactLockfree(scheduled)`, which
succeeds (the hook once, `Pre` to `Q'`, `Pk` back; one commit `X` to `Y`).

**Changes** from `specs-ref`'s `store__restore.lean`: any image, compacted or not, with an unfinished
compaction (`u`), not a fresh backend only (`backendNoCompaction`); over `mvccStorageFor` and the
lessor's writer token (`Lease.lessorState`, 3c's).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.restore()`: the store's fields at the image of `h` (`storeRestored`); the leases attached;
an unfinished compaction resumed (`u`: the hook and the commit), else `Pre` and `X` back. -/
def store.restore.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (B : MvccStorage) (Pk : IProp GF) (le : Loc) (γl : Lease.Names)
    (c : Lease.Cfg) (n : Nat) (ls : Lease.LessorState) (h : KVHist) (u : Bool) (dq : DFrac)
    (f : GoFunc) (Pre Q' Post X Y : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ isStore s γ ∗
      storeRestoring s γ B Pk (Lease.lessorIface le) ∗ mvccStorageFor B Pk h u ∗ schemaVars ∗
      Lease.isLessor le γl c ∗ Lease.lessorState γl n ls ∗
      storageHook B dq f ∗ Pre ∗ hookRun B Pk f Pre Q' ∗ (Q' ={⊤}=∗ Pk ∗ Post) ∗
      X ∗ storageReq B Pk X Y }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"restore")) (Val #()))
  {{ RET #(GoInterface.nil); storeRestored s γ B Pk h ∗ storageHook B dq f ∗
      (if u then iprop(Post ∗ Y) else iprop(Pre ∗ X)) ∗
      ∃ (n' : Nat) (ls' : Lease.LessorState), ⌜RestoreLs ls h.store ls'⌝ ∗ Lease.lessorState γl n' ls' }}

end spec
end Mvcc
end EtcdGrove
end Perennial

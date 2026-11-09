/-
## `MemoryStorage.CreateSnapshot(i, cs, data)`

**Users.** etcd's `bootstrappedWAL.MemoryStorage` (`bootstrap.go:741`: detached, rebuilt from the WAL),
`raftNode.start` (`raft.go:287`, `292`: the batch's snapshot and entries), `EtcdServer.snapshot`
(`server.go:2132`: `CreateSnapshot` at the applied index), `EtcdServer.compact`/`purge`
(`server.go:2180`: `Compact`), `EtcdServer.getSnapshot` (`server.go:755`); the examples' storages
(`kvdurable/storage.go`, a wrapper calling these under its own lock). Snippet: `storage.go` (`ReqSnapshotCompact`). **Proof sketch.** Under the lock: at or
below the stored snapshot, `ErrSnapOutOfDate`; past the last index, or at an index compacted away,
Go panics (`nonissues/raft-memorystorage-createsnapshot-bounds.md`), which the update's precondition
excludes; else the stored snapshot set (the term read at `i`, `cs` cloned, `data` kept) and a clone
returned. **Changes.** Atomic; a non-`nil` `cs` (every client passes one). **Margin.** The storage
keeps `data`: read-only for good. Verify-round (A5 completeness F2, raft-conf-pb's request): `confStateFull` (Go's `ConfState()` sets `AutoLeave`), so the server can store it in a snapshot (`CreateSnapshot`, the merged `MsgSnap`).
-/
module

public import Spec.go_etcd_io.raft.v3.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [ctx_sem : context.Assumptions]

/-- Stores the snapshot at `i` (configuration `cs`, `data`), atomically, and returns a copy; or
`ErrSnapOutOfDate`. -/
def MemoryStorage.CreateSnapshot.spec : Prop :=

  ∀ (ms : Loc) (i : w64) (csp : Loc) (dq : DFrac) (cs : ConfState) (data_sl : GoSlice)
    (data : List w8) (Q : StorState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ RaftPb.confStateFull csp dq cs ∗ ownSlice data_sl data DFrac.discard ∗
      (AU <{ ∃∃ (σ : StorState), memStor ms σ ∗ ⌜uint.nat i ≤ uint.nat σ.snap.index ∨ (σ.off ≤ uint.nat i ∧ uint.nat i ≤ σ.last)⌝ }> @ ⊤, ∅
        <{ memStor ms (σ.createSnapshot (uint.nat i) (some cs) data), COMM Q σ }>) }}
    (App (App (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"CreateSnapshot")) (Val #i)) (Val #csp)) (Val #data_sl))
  {{ (sp : Loc) (err : GoInterface), RET (PairV #sp #err); RaftPb.confStateFull csp dq cs ∗
      ∃ σ, Q σ ∗
      ((⌜err = interface.nil ∧ uint.nat σ.snap.index < uint.nat i⌝ ∗
          snapshotPts sp (DFrac.own 1) (σ.createSnapshot (uint.nat i) (some cs) data).snap) ∨
       (⌜sp = null ∧ uint.nat i ≤ uint.nat σ.snap.index⌝ ∗
          errIs go_etcd_io.raft.v3.ErrSnapOutOfDate err)) }}

end spec
end Raft
end EtcdGrove
end Perennial

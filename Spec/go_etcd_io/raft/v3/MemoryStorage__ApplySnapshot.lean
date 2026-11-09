/-
## `MemoryStorage.ApplySnapshot(snap)`

**Users.** etcd's `bootstrappedWAL.MemoryStorage` (`bootstrap.go:741`: detached, rebuilt from the WAL),
`raftNode.start` (`raft.go:287`, `292`: the batch's snapshot and entries), `EtcdServer.snapshot`
(`server.go:2132`: `CreateSnapshot` at the applied index), `EtcdServer.compact`/`purge`
(`server.go:2180`: `Compact`), `EtcdServer.getSnapshot` (`server.go:755`); the examples' storages
(`kvdurable/storage.go`, a wrapper calling these under its own lock). Snippets: `storage.go`, `readyloop.go`. **Proof sketch.** Under the lock: an older
or equal non-empty stored snapshot refuses it (`ErrSnapOutOfDate`), else the snapshot cloned and the
log reset to it (`StorState.applySnapshot`). **Changes.** Atomic (was `memStorAt`'s modes).
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

/-- Installs snapshot `s`, atomically; `ErrSnapOutOfDate` (nothing changed) if the stored one is as
new. -/
def MemoryStorage.ApplySnapshot.spec : Prop :=

  ∀ (ms : Loc) (sp : Loc) (dq : DFrac) (s : Snapshot) (Q : StorState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ snapshotPts sp dq s ∗ (AU <{ ∃∃ (σ : StorState), memStor ms σ }> @ ⊤, ∅
        <{ memStor ms (σ.applySnapshot s), COMM Q σ }>) }}
    (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"ApplySnapshot")) (Val #sp))
  {{ (err : GoInterface), RET #err; snapshotPts sp dq s ∗ ∃ σ, Q σ ∗
      ((⌜err = interface.nil ∧ σ.applySnapshotErr s = false⌝) ∨
       (⌜σ.applySnapshotErr s = true⌝ ∗ errIs go_etcd_io.raft.v3.ErrSnapOutOfDate err)) }}

end spec
end Raft
end EtcdGrove
end Perennial

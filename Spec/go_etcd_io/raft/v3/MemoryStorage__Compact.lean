/-
## `MemoryStorage.Compact(i)`

**Users.** etcd's `bootstrappedWAL.MemoryStorage` (`bootstrap.go:741`: detached, rebuilt from the WAL),
`raftNode.start` (`raft.go:287`, `292`: the batch's snapshot and entries), `EtcdServer.snapshot`
(`server.go:2132`: `CreateSnapshot` at the applied index), `EtcdServer.compact`/`purge`
(`server.go:2180`: `Compact`), `EtcdServer.getSnapshot` (`server.go:755`); the examples' storages
(`kvdurable/storage.go`, a wrapper calling these under its own lock). Snippet: `storage.go` (`ReqSnapshotCompact`). **Proof sketch.** Under the lock: at or
below the compaction point, `ErrCompacted`; past the last index Go panics (excluded by the update's
precondition); else a new slice from `i` (`StorState.compact`). **Changes.** Atomic.
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

/-- Compacts up to `i`, atomically; `ErrCompacted` (nothing changed) at or below the compaction
point. -/
def MemoryStorage.Compact.spec : Prop :=

  ∀ (ms : Loc) (i : w64) (Q : StorState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ (AU <{ ∃∃ (σ : StorState), memStor ms σ ∗ ⌜uint.nat i ≤ σ.last⌝ }> @ ⊤, ∅
        <{ memStor ms (σ.compact (uint.nat i)), COMM Q σ }>) }}
    (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"Compact")) (Val #i))
  {{ (err : GoInterface), RET #err; ∃ σ, Q σ ∗
      ((⌜err = interface.nil ∧ σ.off < uint.nat i⌝) ∨
       (⌜uint.nat i ≤ σ.off⌝ ∗ errIs go_etcd_io.raft.v3.ErrCompacted err)) }}

end spec
end Raft
end EtcdGrove
end Perennial

/-
## `MemoryStorage.SetHardState(st)`

**Users.** etcd's `bootstrappedWAL.MemoryStorage` (`bootstrap.go:741`: detached, rebuilt from the WAL),
`raftNode.start` (`raft.go:287`, `292`: the batch's snapshot and entries), `EtcdServer.snapshot`
(`server.go:2132`: `CreateSnapshot` at the applied index), `EtcdServer.compact`/`purge`
(`server.go:2180`: `Compact`), `EtcdServer.getSnapshot` (`server.go:755`); the examples' storages
(`kvdurable/storage.go`, a wrapper calling these under its own lock). Snippet: `storage.go`. **Proof sketch.** Under the lock, the pointer stored; the
update fired there (on an attached storage, the client got it from `stor_setHardState`).
**Changes.** Atomic (was over the detached or attached modes `memStorAt`). **Margin.** The storage
keeps the pointer: the caller gives up writing it (`hsPtr` is read-only).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.Api

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

/-- Stores hard state `hs`, atomically. -/
def MemoryStorage.SetHardState.spec : Prop :=

  ∀ (ms : Loc) (p : Loc) (hs : HardState) (Q : StorState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ hsPtr p DFrac.discard hs ∗ (AU <{ ∃∃ (σ : StorState), memStor ms σ }> @ ⊤, ∅
        <{ memStor ms (σ.setHardState hs), COMM Q σ }>) }}
    (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"SetHardState")) (Val #p))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗ ∃ σ, Q σ }}

end spec
end Raft
end EtcdGrove
end Perennial

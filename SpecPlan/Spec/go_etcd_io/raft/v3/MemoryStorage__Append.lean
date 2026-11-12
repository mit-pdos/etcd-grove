/-
## `MemoryStorage.Append(entries)`

**Users.** etcd's `bootstrappedWAL.MemoryStorage` (`bootstrap.go:741`: detached, rebuilt from the WAL),
`raftNode.start` (`raft.go:287`, `292`: the batch's snapshot and entries), `EtcdServer.snapshot`
(`server.go:2132`: `CreateSnapshot` at the applied index), `EtcdServer.compact`/`purge`
(`server.go:2180`: `Compact`), `EtcdServer.getSnapshot` (`server.go:755`); the examples' storages
(`kvdurable/storage.go`, a wrapper calling these under its own lock). Snippets: `storage.go`, `readyloop.go`. **Proof sketch.** Empty: returns at once
(the update fired with no change). Else under the lock: truncate below the first index, then
replace from the first new index or extend (`StorState.append`); a gap panics, which the update's
precondition excludes. **Changes.** Atomic over the contents (was `memLog`/`memEnd` ranges).
**Margin.** The storage keeps the entry pointers (read-only for good).
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

/-- Appends `es` (at index `k` on), atomically. -/
def MemoryStorage.Append.spec : Prop :=

  ∀ (ms : Loc) (sl : GoSlice) (k : Nat) (es : List LogEntry) (Q : StorState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ entriesRO sl k es ∗
      (AU <{ ∃∃ (σ : StorState), memStor ms σ ∗ ⌜(σ.append k es).isSome ∧ k + es.length < 2 ^ 64⌝ }> @ ⊤, ∅
        <{ memStor ms ((σ.append k es).getD σ), COMM Q σ }>) }}
    (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"Append")) (Val #sl))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗ ∃ σ, Q σ }}

end spec
end Raft
end EtcdGrove
end Perennial

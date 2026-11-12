/-
## `MemoryStorage.lastIndex()` (internal)

**Users.** `MemoryStorage`'s `LastIndex`, `Entries`, `CreateSnapshot`, `Compact`, `Append` (`storage.go`), under the lock. **Proof sketch.** Mirrors the
code: `ms.ents[0].GetIndex()` (the dummy entry, at the compaction point) plus `len(ents) - 1`; `ents` is never
empty. **Changes.** Restored (verify-round, A4 completeness F4: `specs-ref` had it, with a linked
proof; the locked methods' sketches call it). **Margin.** None.
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

/-- (internal) The last stored index, from the locked `ents` field (its first entry the dummy at index `k`). -/
def MemoryStorage.lastIndex.spec : Prop :=
  ∀ (ms : Loc) (sl : GoSlice) (dq : DFrac) (k : Nat) (es : List LogEntry), es ≠ [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      ms.[go_etcd_io.raft.v3.MemoryStorage, go!"ents"] ↦{dq} sl ∗ entriesRO sl k es }}
    (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"lastIndex")) (Val #()))
  {{ RET #(W64 (k + es.length - 1)); ms.[go_etcd_io.raft.v3.MemoryStorage, go!"ents"] ↦{dq} sl ∗ entriesRO sl k es }}

end spec
end Raft
end EtcdGrove
end Perennial

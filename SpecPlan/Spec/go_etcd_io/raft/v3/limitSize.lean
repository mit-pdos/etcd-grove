/-
## `limitSize(ents, maxSize)` (internal)

**Users**: `MemoryStorage.Entries` (`storage.go:161`, R1: needs a non-empty prefix of a non-empty
list), `slice`. **Proof sketch**: `proto.Size` of each entry (2a's); the prefix shares the array.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/limitSize.lean`: over `entriesRO` (persistent, so nothing to give back).
**Margin**: the size bound itself (sizes are not modeled).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiLog

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

/-- (internal) A prefix of `ents`, non-empty if `ents` is. -/
def limitSize.spec : Prop :=
  ∀ (sl : GoSlice) (k : Nat) (es : List LogEntry) (mx : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ entriesRO sl k es }}
    (App (App (Val (@! go_etcd_io.raft.v3.limitSize)) (Val #sl)) (Val #mx))
  {{ (sl' : GoSlice), RET #sl'; ∃ n, ⌜n ≤ es.length ∧ (es ≠ [] → 1 ≤ n)⌝ ∗
      entriesRO sl' k (es.take n) }}

end spec
end Raft
end EtcdGrove
end Perennial

/-
## `entsSize(ents)` (internal)

**Users**: `slice`, `acceptReady` (`rawnode.go:434`), `MsgStorageApplyResp` (`raft.go:1226`). The
sum of `proto.Size` of each entry (2a's `proto`: some size, no panic), wrapping. Only budgets use it.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/entsSize.lean`: unchanged (the size is not modeled).
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

/-- (internal) The entries' encoded size (unspecified). -/
def entsSize.spec : Prop :=
  ∀ (sl : GoSlice) (k : Nat) (es : List LogEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ entriesRO sl k es }}
    (App (Val (@! go_etcd_io.raft.v3.entsSize)) (Val #sl))
  {{ (n : w64), RET #n; True }}

end spec
end Raft
end EtcdGrove
end Perennial

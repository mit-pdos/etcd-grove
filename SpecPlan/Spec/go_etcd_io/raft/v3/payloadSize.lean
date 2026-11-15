/-
## `payloadSize(e)` (internal)

**Users**: `payloadsSize`, `appendEntry`'s uncommitted budget. Mirrors the code.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/payloadSize.lean`.
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

/-- (internal) The length of the entry's data. -/
def payloadSize.spec : Prop :=
  ∀ (p : Loc) (k : Nat) (e : LogEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ entryRO p k e }}
    (App (Val (@! go_etcd_io.raft.v3.payloadSize)) (Val #p))
  {{ RET #(W64 e.data.length); True }}

end spec
end Raft
end EtcdGrove
end Perennial

/-
## `newReadOnly(option)` (internal)

**Users**: `newRaft` (`raft.go:462`), `reset` (`raft.go:827`, on every term change). Mirrors the code.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/newReadOnly.lean`: over `ReadOnlyState`.
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

/-- (internal) An empty read-index queue. -/
def newReadOnly.spec : Prop :=
  ∀ (opt : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val (@! go_etcd_io.raft.v3.newReadOnly)) (Val #opt))
  {{ (ro : Loc), RET #ro; readOnly ro ⟨opt, ∅, [], W64 0⟩ }}

end spec
end Raft
end EtcdGrove
end Perennial

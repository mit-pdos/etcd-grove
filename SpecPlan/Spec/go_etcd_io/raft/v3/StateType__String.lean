/-
## `StateType.String()` (internal)

Logging. Mirrors the code: `stmap[st]`, in bounds for the four roles. **Changes.** New.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

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

/-- (internal) A role's name. -/
def StateType.String.spec : Prop :=
  ∀ (st : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ⌜uint.nat st < 4⌝ }}
    (App (Val (st @!! go_etcd_io.raft.v3.StateType.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec
end Raft
end EtcdGrove
end Perennial

/-
## `outgoing(voters)` (internal)

**Users.** confchange's functions. Mirrors the code: the second
half.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.confchange.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ConfChange

open Iris Iris.BI
open Classical Tracker

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.confchange.Assumptions]

/-- (internal) The outgoing half. -/
def outgoing.spec : Prop :=
  ∀ (c : go_etcd_io.raft.v3.quorum.JointConfig) (m0 m1 : GoMap),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ ⌜c.arr = [m0, m1]⌝ }}
    (App (Val #(functions go_etcd_io.raft.v3.confchange.outgoing [])) (Val #c))
  {{ RET #m1; True }}

end spec
end ConfChange
end EtcdGrove
end Perennial

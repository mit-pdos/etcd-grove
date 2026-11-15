/-
## `Status.String()` (`status.go`)

Logging. **Proof sketch.** `MarshalJSON` (no error, so its `Panicf` is not reached). **Changes.**
New (round 1).
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

/-- The status's text. -/
def Status.String.spec : Prop :=
  ∀ (s : go_etcd_io.raft.v3.Status),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ statusOwn s }}
    (App (Val (s @!! go_etcd_io.raft.v3.Status.ty @!! go!"String")) (Val #()))
  {{ (str : GoString), RET #str; statusOwn s }}

end spec
end Raft
end EtcdGrove
end Perennial

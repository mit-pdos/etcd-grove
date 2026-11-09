/-
`(*lessor).isPrimary()` (`lessor.go:263`), an internal helper's spec (mirrors the code). **Users**:
`Grant`, `Checkpoint`, `Renew`, the run loop, under `le.mu` (either mode). **Proof sketch**:
`demotec != nil`. **Changes** (from `specs-ref`'s `lessor__isPrimary.lean`): over `lessorFields`;
the answer any boolean (the primary flag is not modelled). **Margin**: the flag.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Internal

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Lease

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **Whether the lessor is primary** (under its lock). -/
def lessor.isPrimary.spec : Prop :=
  ∀ (le : Loc) (c : Cfg) (dq : DFrac) (ls : LessorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorFields le c dq ls }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"isPrimary")) (Val #()))
  {{ (b : Bool), RET #b; lessorFields le c dq ls }}

end spec
end Lease
end EtcdGrove
end Perennial

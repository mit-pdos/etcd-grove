/-
`(*Lease).forever()` (`lease.go:92`), an internal helper's spec (mirrors the code). **Users**:
`Grant` (not primary), `Demote`, under `le.mu`. **Proof sketch**: the package variable `forever`
loaded and stored under `expiryMu` (`leaseExpiry`). **Changes** (from `specs-ref`'s
`Lease__forever.lean`): over `leaseExpiry`. **Margin**: the expiry (time).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Internal

set_option autoImplicit false
set_option linter.iris.dupNamespace false

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

/-- **Set the object's expiry to `forever`.** -/
def Lease.forever.spec : Prop :=
  ∀ (l : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ leaseExpiry l }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.Lease.ty @!!
      go!"forever")) (Val #()))
  {{ RET #(); True }}

end spec
end Lease
end EtcdGrove
end Perennial

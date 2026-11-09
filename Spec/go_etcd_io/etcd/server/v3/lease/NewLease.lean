/-
`NewLease(id, ttl)` (`lease.go:42`), an internal helper's spec (mirrors the code). **Users**:
`Grant` (`lessor.go:292`). **Proof sketch**: a composite literal with a fresh map and channel.
**Changes** (from `specs-ref`'s `NewLease.lean`): over `leaseFresh`. **Margin**: none.
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

/-- **A fresh `*Lease`** of id `id` and TTL `ttl`. -/
def NewLease.spec : Prop :=
  ∀ (id ttl : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.lease.NewLease)) (Val #id)) (Val #ttl))
  {{ (l : Loc), RET #l; leaseFresh l (sint.Z id) (sint.Z ttl) }}

end spec
end Lease
end EtcdGrove
end Perennial

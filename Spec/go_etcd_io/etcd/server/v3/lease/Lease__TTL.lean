/-
## `(*Lease).TTL()` (`lease.go:64`)

**Users.** The applier's `LeaseGrant` (`apply/backend.go:84`: the response's TTL), 2c's
`leaseTimeToLive` (`v3_server.go:652`: `GrantedTTL`). Snippet `lessor.go` (`ReqGrantLookup`).

**Proof sketch.** Reads `l.ttl` without a lock: frozen once the object is published (`Grant` raises
it before `leaseMap[id] = l`), `leaseObj`'s `ttl ↦□`.

**Changes** (from `specs-ref`'s `Lease__TTL.lean`, a field points-to): over `leaseObj`.
**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Api

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

/-- **The object's granted TTL.** -/
def Lease.TTL.spec : Prop :=
  ∀ (γ : Names) (l : Loc) (id ttl : Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ leaseObj γ l id ttl }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.Lease.ty @!!
      go!"TTL")) (Val #()))
  {{ (t : w64), RET #t; ⌜sint.Z t = ttl⌝ }}

end spec
end Lease
end EtcdGrove
end Perennial

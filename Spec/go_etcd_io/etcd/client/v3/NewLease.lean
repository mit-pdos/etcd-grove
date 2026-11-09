/-
`clientv3.NewLease` (`client/v3/lease.go`).

Users: `newClient` (`client.Lease = NewLease(client)`).

Proof sketch: `RetryLeaseClient(c)` (its spec: `retryLeaseHandle`, from `clientConnOk`), then
`NewLeaseFromLeaseClient` with the client and `DialTimeout + 1s`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/NewLease.lean`: restated over `clientCore`.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiLease

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewLease(c)`: a lessor of the client's cluster and principal. -/
def NewLease.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientCore c γ who }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewLease)) (Val #c))
  {{ (v : GoInterface), RET #v; ∃ l : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #l⌝ ∗
      lessorHandle l c γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial

/-
`clientv3.RetryLeaseClient` (`client/v3/retry.go`).

Users: `NewLease`.

Proof sketch: `pb.NewLeaseClient(c.conn)` (the stub over `connOk`: 2a/3h), wrapped and persisted.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/RetryLeaseClient.lean`: restated.

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

/-- `RetryLeaseClient(c)`: a `*retryLeaseClient` over the client's connection. -/
def RetryLeaseClient.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientConnOk c γ who }}
    (App (Val (@! go_etcd_io.etcd.client.v3.RetryLeaseClient)) (Val #c))
  {{ (v : GoInterface), RET #v; ∃ r : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryLeaseClient.ty) #r⌝ ∗
      retryLeaseHandle r γ who }}

end spec

end ClientV3
end EtcdGrove
end Perennial

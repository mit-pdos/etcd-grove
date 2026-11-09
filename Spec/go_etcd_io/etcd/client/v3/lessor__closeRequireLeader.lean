/-
`(*clientv3.lessor).closeRequireLeader` (`client/v3/lease.go`).

Users: `recvKeepAliveLoop` (on `ErrNoLeader`).

Proof sketch: under `l.mu`, for each entry, reads each context's outgoing metadata
(`metadata.FromOutgoingContext`, 2a's metadata spec over `ctxOk`), closes the channels of those
with `MetadataRequireLeaderKey` set (their close tokens, in the entry) and rebuilds the entry's
slices without them.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/lessor__closeRequireLeader.lean`: restated over `lessorHandle`.

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

/-- `l.closeRequireLeader()`: closes the keep-alive channels whose contexts require a leader. -/
def lessor.closeRequireLeader.spec : Prop :=
  ∀ (l c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l c γ who ∗ clientReady c }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"closeRequireLeader")) (Val #()))
  {{ (v : val), RET v; True }}

end spec

end ClientV3
end EtcdGrove
end Perennial

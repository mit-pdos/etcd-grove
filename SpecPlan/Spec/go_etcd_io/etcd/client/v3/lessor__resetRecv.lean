/-
`(*clientv3.lessor).resetRecv` (`client/v3/lease.go`).

Users: `recvKeepAliveLoop`.

Proof sketch: a cancellable child of `stopCtx`; `l.remote.LeaseKeepAlive(sctx, append(l.callOpts,
withMax(0))...)` (`callOptsOk_append` with `withMax.spec`; `remoteLeaseAt_keepAlive`); on success,
under `l.mu`, cancels the previous stream and stores this one, then starts `sendKeepAliveLoop` with
the sending half (`kaSendAt`), returning the receiving half.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/lessor__resetRecv.lean`: restated over
`lessorHandle` and the stream halves.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.ApiLease

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

/-- `l.resetRecv()`: a new keep-alive stream's receiving half (its sender running), or an error. -/
def lessor.resetRecv.spec : Prop :=
  ∀ (l c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l c γ who ∗ clientReady c }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"resetRecv")) (Val #()))
  {{ (sc err : GoInterface), RET (PairV #sc #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ g, kaRecvAt sc g) ∨ (⌜sc = GoInterface.nil⌝ ∗ ∃ k, callErr err k) }}

end spec

end ClientV3
end EtcdGrove
end Perennial

/-
`(*clientv3.lessor).sendKeepAliveLoop` (`client/v3/lease.go`).

Users: `resetRecv` (a goroutine per stream).

Proof sketch: a loop: under `l.mu`, the ids whose next keep-alive is due; `Send` of a request for
each (`kaSendAt_send`; an error: `l.lg.Warn`, return); waits `retryConnWait`, the stream's context
(`kaSendAt_context`), `donec` or `stopCtx`. Carries `kaSendAt`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/lessor__sendKeepAliveLoop.lean`: restated over
`lessorHandle` and the sending half.

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

/-- `l.sendKeepAliveLoop(stream)`: sends the due keep-alives until the stream or the lessor ends. -/
def lessor.sendKeepAliveLoop.spec : Prop :=
  ∀ (l c : Loc) (γ : Cluster) (who : Principal) (sc : GoInterface) (g : Grpc.StreamName) (ids : List Int),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l c γ who ∗ clientReady c ∗ kaSendAt sc g ids }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"sendKeepAliveLoop")) (Val #sc))
  {{ RET #(); True }}

end spec

end ClientV3
end EtcdGrove
end Perennial

/-
`(*clientv3.lessor).Close` (`client/v3/lease.go`).

Users: `Client.Close` (`client.go`); snippet `clientv3client/lifecycle.go` (`ReqCloseThenCalls`).

Proof sketch: `l.stopCancel()` (cancels `stopCtx`: the loops see it), `firstKeepAliveOnce.Do(close
donec)` (if the loops never started: `donec`'s close token is the `Once`'s, the receive loop's
otherwise), then receives from `donec` (closed by the receive loop's deferred cleanup once it sees
the cancellation). Idempotent: a second `Close` finds `donec` closed.

Changes: new (no old spec; the old `Client.Close` spec was `True`).

Margin: the keep-alive channels are closed by the receive loop's cleanup right after `donec`
(under `l.mu`), so not necessarily when `Close` returns.
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

/-- `l.Close()`: the keep-alive loops stopped; `nil`. -/
def lessor.Close.spec : Prop :=
  ∀ (l : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ lessorHandle l γ who }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial

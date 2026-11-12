/-
`(*clientv3.Client).Close` (`client/v3/client.go`).

Users: every client program's teardown (`examples/lib/*`, Kubernetes' `etcd3.go` destroy func,
`compactor.client.Close()`), `newClient`'s error paths; snippet `clientv3client/lifecycle.go`
(`ReqNewWrapClose`: calls after `Close` fail, never panic).

Proof sketch: `c.cancel()` (the client's context: its loops and every call made with a child of
`c.Ctx()` see it done); `c.Watcher.Close()` (1b's `watcherAt` bundle), `c.Lease.Close()` (`leaseAt`:
the keep-alive loops stopped), `c.conn.Close()` (2a: later attempts fail, a second `Close` returns
an error) through `ContextError`. Every handle stays valid (persistent): a call after `Close` is a
call whose attempts fail (`indefCall`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__Close.lean` (`True` over the old
client): over W0's `clientRest` (round 1: a client whose `KV` another holds closes too); concurrent and repeated `Close`s are allowed (each piece is idempotent).

Margin: outstanding calls are not waited for: they return an indefinite error (`Canceled`, the
connection closing) whenever they notice. The goroutines it stops hold no resource a caller gave
(the client takes no counted resource), so it gives nothing back.
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

/-- `c.Close()`: the client stopped; any error. -/
def Client.Close.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientRest c γ who }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; True }}

end spec

end ClientV3
end EtcdGrove
end Perennial

/-
`clientv3.WithRequireLeader` (`client/v3/ctx.go`).

Users: Kubernetes' store (`etcd3/store.go`: its watch contexts), `client/v3/concurrency` and 1c (`lessor`'s keep-alive contexts, `clientv3/watch.go`), the users' watches.

Proof sketch: grpc's `metadata.FromOutgoingContext`, `metadata.Pairs`, `MD.Copy`, `MD.Set`, `metadata.NewOutgoingContext` (the gRPC boundary, 2a: `NewOutgoingContext` returns a `WithValue` context over its argument, `ctxWithValues`), and `rpctypes`' metadata key constants.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/WithRequireLeader.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `WithRequireLeader(ctx)`: a context with the require-leader metadata, done with `ctx`. -/
def WithRequireLeader.spec : Prop :=
  ∀ (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ Context.ctxOk ctx }}
    (App (Val (@! go_etcd_io.etcd.client.v3.WithRequireLeader)) (Val #ctx))
  {{ (ctx' : GoInterface), RET #ctx'; Context.ctxOk ctx' ∗ Context.ctxWithValues ctx ctx' ∗
      ctxRequireLeader ctx' ∗ □ (∀ dflt p, ctxPrin dflt ctx p -∗ ctxPrin dflt ctx' p) }}

end spec

end ClientV3
end EtcdGrove
end Perennial

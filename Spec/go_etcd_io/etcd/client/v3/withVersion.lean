/-
`clientv3.withVersion` (`client/v3/ctx.go`).

Users: the client's interceptors (1c: every call carries the client's API version).

Proof sketch: as `WithRequireLeader`, with `version.APIVersion`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/withVersion.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `withVersion(ctx)`: a context with the client-version metadata, done with `ctx`. -/
def withVersion.spec : Prop :=
  ∀ (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ Context.ctxOk ctx }}
    (App (Val (@! go_etcd_io.etcd.client.v3.withVersion)) (Val #ctx))
  {{ (ctx' : GoInterface), RET #ctx'; Context.ctxOk ctx' ∗ Context.ctxWithValues ctx ctx' ∗
      □ (∀ dflt p, ctxPrin dflt ctx p -∗ ctxPrin dflt ctx' p) }}

end spec

end ClientV3
end EtcdGrove
end Perennial

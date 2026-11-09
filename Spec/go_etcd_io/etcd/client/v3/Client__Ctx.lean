/-
`(*clientv3.Client).Ctx` (`client/v3/client.go`).

Users: `concurrency` (`NewSession`'s default context, `Mutex`, `Election`, `STM`), `leasing.NewKV`,
Kubernetes' `store.go` (feature check); snippet `clientv3client/lifecycle.go` (`ReqCtxPut`).

Proof sketch: reads `c.ctx` (read-only in `clientPre`): the client's cancellable child of the
configuration's context (`ctxOk`; `ctxPrin _ who`: `cfgOk`'s, kept by `ctxPrin_child`).

Changes: new (no old spec; the old `Client.Ctx` was used by the concurrency proofs as an
`isContext`): a context W0's KV contract accepts as `who`'s (W0's `req`, item 4).

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

/-- `c.Ctx()`: the client's context, carrying `who`'s requests. -/
def Client.Ctx.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientPre c γ who }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Ctx")) (Val #()))
  {{ (ctx : GoInterface), RET #ctx; Context.ctxOk ctx ∗ ctxPrin ctx who }}

end spec

end ClientV3
end EtcdGrove
end Perennial

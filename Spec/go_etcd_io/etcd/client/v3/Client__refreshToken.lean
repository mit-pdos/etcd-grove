/-
`(*clientv3.Client).refreshToken` (`client/v3/retry_interceptor.go`).

Users: the unary interceptor (after `shouldRefreshToken`), the retrying stream (unused: see the
report).

Proof sketch: no token bundle (TLS or no credentials): `nil` (the interceptor then resends: a stale
auth revision is retried as is); else `getToken`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/Client__refreshToken.lean`.

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

/-- `c.refreshToken(ctx)`: as `getToken`. -/
def Client.refreshToken.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface) (p : Principal),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientCore c γ who ∗ clientReady c ∗ Context.ctxOk ctx ∗ ctxPrin who ctx p }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"refreshToken")) (Val #ctx))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∨ indefCall err ∨
      ∃ e, callErr err (.etcd e) ∗ ⌜e.refusal = true⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial

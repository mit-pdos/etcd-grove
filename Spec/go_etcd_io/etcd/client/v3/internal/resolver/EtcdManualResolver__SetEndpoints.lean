/-
`(*EtcdManualResolver).SetEndpoints(eps)` (`client/v3/internal/resolver`, names only; item 5).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `r.SetEndpoints(eps)` of a resolver not yet dialed, with the endpoints `eps` (read-only): the
resolver has them. -/
abbrev resolver.EtcdManualResolver.SetEndpoints.spec : Prop :=
  ∀ (r : Loc) (eps0 : List GoString) (sl : GoSlice) (eps : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver ∗
      etcdResolverOwn r eps0 ∗ sl ↦*□ eps }}
    (App (Val (r @!! go.GoType.PointerType
      go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver.ty @!! go!"SetEndpoints"))
      (Val #sl))
  {{ RET #(); etcdResolverOwn r eps }}

end spec

end EtcdGrove
end Perennial

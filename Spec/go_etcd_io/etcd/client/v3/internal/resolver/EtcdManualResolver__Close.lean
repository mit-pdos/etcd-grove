/-
`(*EtcdManualResolver).Close()` (`client/v3/internal/resolver`, names only: grpc's `manual.Resolver`'s,
promoted; item 5: `newClient` closes the resolver when the dial fails). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `r.Close()` of a resolver whose closing right the caller holds (`etcdResolverCloser`, which
`New` gives; prove-grpc3, 2026-11-21: until then no premise, as an axiom, which a nil or
foreign `r` refutes) returns. -/
abbrev resolver.EtcdManualResolver.Close.spec : Prop :=
  ∀ (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver ∗
      etcdResolverCloser r }}
    (App (Val (r @!! go.GoType.PointerType
      go_etcd_io.etcd.client.v3.internal.resolver.EtcdManualResolver.ty @!! go!"Close")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial

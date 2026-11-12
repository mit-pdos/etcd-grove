/-
Proof of `Spec/go_etcd_io/etcd/client/v3/internal/resolver/New.lean`: a trust-boundary axiom (item 5, client construction). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.internal.resolver.New

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (item 5): `resolver.New(eps...)` returns `&EtcdManualResolver{Resolver:
manual.NewBuilderWithScheme(Schema), endpoints: eps}` (`client/v3/internal/resolver/resolver.go`):
it keeps the slice, which its holder never writes. -/
axiom resolver.New.wp_proof : resolver.New.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

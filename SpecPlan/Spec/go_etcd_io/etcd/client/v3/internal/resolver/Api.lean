/-
# `client/v3/internal/resolver` (batch 1c)

* `resolverAt r eps` (exclusive: `SetEndpoints` writes its field; the client holds it under
  `epMu`): an `*EtcdManualResolver` with the endpoints `eps` (read-only strings), its grpc manual
  resolver's state (2a: `UpdateState` once grpc has built it).
-/
module

public import GeneratedProof.go_etcd_io.etcd.client.v3.internal.resolver
public import SpecPlan.Spec.PkgInit.go_etcd_io.etcd.client.v3.internal.resolver

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Resolver

open Iris Iris.BI

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A resolver with the endpoints `eps`** (exclusive). -/
opaque resolverAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (r : Loc) (eps : List GoString) : IProp GF := iprop(True)

end res

end Resolver
end EtcdGrove
end Perennial

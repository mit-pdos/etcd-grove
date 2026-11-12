/-
**Trust boundary**: `withVersion` returns a value context of its argument, with the API version set in its outgoing metadata (an axiom; see `Spec/go_etcd_io/etcd/client/v3/withVersion.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.withVersion

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **Trust boundary**: `withVersion` returns a value context of its argument, with the API version
set in its outgoing metadata. -/
axiom withVersion.wp_proof : withVersion.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

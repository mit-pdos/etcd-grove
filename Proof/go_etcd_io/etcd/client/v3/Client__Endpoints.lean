/-
**Trust boundary**: the client's `Endpoints` returns a copy of its endpoints (an axiom; see `Spec/go_etcd_io/etcd/client/v3/Client__Endpoints.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__Endpoints

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

/-- **Trust boundary**: the client's `Endpoints` returns a new slice, a copy of `c.endpoints`
(`make` and `copy` under `c.epMu.RLock()`). -/
axiom Client.Endpoints.wp_proof : Client.Endpoints.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

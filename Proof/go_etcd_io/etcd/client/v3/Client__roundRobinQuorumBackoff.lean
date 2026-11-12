/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__roundRobinQuorumBackoff.lean`: a trust-boundary axiom (item 5, client construction). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__roundRobinQuorumBackoff

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
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **Trust boundary** (item 5): `roundRobinQuorumBackoff(w, j)` returns a closure that reads
`len(c.Endpoints())` (an `RWMutex` read), computes `quorum = n/2 + 1` (at least 1: no division
by zero), logs at debug level with `c.GetLogger()` (non-nil, `isClientLogger`) and returns
`jitterUp(w, j)` (float arithmetic and `rand.Float64`, which return) or `0`: it returns. -/
axiom Client.roundRobinQuorumBackoff.wp_proof : Client.roundRobinQuorumBackoff.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

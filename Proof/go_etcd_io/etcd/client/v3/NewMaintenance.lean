/-
Proof of `Spec/go_etcd_io/etcd/client/v3/NewMaintenance.lean`: a trust-boundary axiom (item 5, client construction). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.NewMaintenance

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

/-- **Trust boundary** (item 5): `NewMaintenance(c)` returns `&maintenance{lg: c.GetLogger(), dial: <a closure over c>, remote:
RetryMaintenanceClient(c, c.conn), callOpts: c.callOpts}`: allocations and reads of `c`'s
fields, which `New` set and never writes again; it returns. -/
axiom NewMaintenance.wp_proof : NewMaintenance.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

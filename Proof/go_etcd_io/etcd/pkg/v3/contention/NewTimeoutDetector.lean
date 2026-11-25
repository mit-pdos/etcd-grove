/-
The trust boundary: `contention.NewTimeoutDetector` (names-only; premises to axioms, item D,
2026-11-24); see the spec file for the statement and why it is true.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.contention.NewTimeoutDetector

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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The trust boundary**: `contention.NewTimeoutDetector` and its detector's methods, as the spec
states them (interim, until the package is translated with its bodies). -/
axiom contention.NewTimeoutDetector.wp_proof : contention.NewTimeoutDetector.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

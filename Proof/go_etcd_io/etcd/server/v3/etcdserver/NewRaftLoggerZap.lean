/-
The trust boundary: `NewRaftLoggerZap` (names-only; premises to axioms, item C, 2026-11-24); see the
spec file for the statement and why it is true.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewRaftLoggerZap

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

/-- **The trust boundary**: `NewRaftLoggerZap`, as the spec states it (interim, until zap's specs). -/
axiom NewRaftLoggerZap.wp_proof : NewRaftLoggerZap.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

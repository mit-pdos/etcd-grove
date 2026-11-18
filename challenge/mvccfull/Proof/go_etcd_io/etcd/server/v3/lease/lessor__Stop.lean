/-
The trust boundary: `(*lease.lessor).Stop()` (names-only). Lean-first (no Rocq counterpart);
R2b-3c part 2 (2026-11-04, the user's approval), an axiom: why the statement is true of the Go code
is in its spec's docstring.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Stop

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
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

axiom lease.lessor.Stop.wp_proof : lease.lessor.Stop.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

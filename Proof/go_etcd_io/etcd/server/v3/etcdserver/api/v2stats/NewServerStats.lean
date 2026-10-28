/-
The trust boundary: `v2stats.NewServerStats(name, id)` (`server.go`): names-only. Lean-first (no Rocq counterpart); the
server-construction unit, stage N0 (2026-10-16), for `NewServer`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.NewServerStats

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom v2stats.NewServerStats.wp_proof : v2stats.NewServerStats.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

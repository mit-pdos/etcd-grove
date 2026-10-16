/-
The trust boundary: `v2stats.NewLeaderStats(lg, id)`: names-only. Lean-first (no Rocq counterpart); the
server-construction unit, stage N0 (2026-10-16), for `NewServer`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats.NewLeaderStats

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom v2stats.NewLeaderStats.wp_proof : v2stats.NewLeaderStats.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

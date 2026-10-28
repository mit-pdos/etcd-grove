/-
The trust boundary: `config.ServerConfig.PeerDialTimeout` (`config.go`: a duration computed from two fields): names-only. Lean-first (no Rocq counterpart); the
server-construction unit, stage N0 (2026-10-16), for `NewServer`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__PeerDialTimeout

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

axiom config.ServerConfig.PeerDialTimeout.wp_proof : config.ServerConfig.PeerDialTimeout.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial

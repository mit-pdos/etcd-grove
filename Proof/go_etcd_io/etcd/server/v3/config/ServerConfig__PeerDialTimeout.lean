/-
`config.ServerConfig.PeerDialTimeout` (`config.go`: `time.Second + Duration(ElectionTicks *
int(TickMs)) * time.Millisecond`, the fields read-only), verified: translated with its body
(`Code/go_etcd_io/etcd/server/v3/config.toml`), as `ElectionTimeout`. Until 2026-11-18 a
trust-boundary axiom (the server-construction unit, stage N0, 2026-10-16).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__PeerDialTimeout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem config.ServerConfig.PeerDialTimeout.wp_proof :
    config.ServerConfig.PeerDialTimeout.spec (GF := GF) (hG := hG) := by
  intro c et tm
  wp_start as ⟨#Het, #Htm⟩
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial

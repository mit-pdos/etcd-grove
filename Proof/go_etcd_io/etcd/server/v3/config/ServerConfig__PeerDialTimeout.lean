/-
Proof of `Spec/go_etcd_io/etcd/server/v3/config/ServerConfig__PeerDialTimeout.lean`
(`time.Second + time.Duration(c.ElectionTicks*int(c.TickMs))*time.Millisecond`: straight-line
arithmetic that wraps; until 2026-11-19 a trust-boundary axiom). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__PeerDialTimeout

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.config.Assumptions]

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

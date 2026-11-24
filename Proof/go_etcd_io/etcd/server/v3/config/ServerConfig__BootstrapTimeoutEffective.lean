/-
Proof of `config.ServerConfig.BootstrapTimeoutEffective.spec` (claim #34, stage 2, 2026-11-25).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__BootstrapTimeoutEffective

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.config.Assumptions]

theorem config.ServerConfig.BootstrapTimeoutEffective.wp_proof :
    config.ServerConfig.BootstrapTimeoutEffective.spec (GF := GF) (hG := hG) := by
  intro p cfg
  wp_start as #Hbt
  wp_auto
  wp_if_destruct
  · wp_auto
    iapply HΦ; itrivial
  · wp_auto
    iapply HΦ; itrivial

end proof

end EtcdGrove
end Perennial

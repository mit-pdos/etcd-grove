/-
Proof of `Spec/github_com/prometheus/client_golang/prometheus/Register.lean` (prom-registry,
2026-11-22, notes/prom-registry.md): `Register` runs the trusted glue
(`TrustedCode/github_com/prometheus/client_golang/prometheus.lean`), which registers the collector's
descriptors (`collectorDescs`, what its constructor says: `collectorDescsAre`) with the model's
registry (`promreg.Registry.Register`, verified) and returns `nil` when the model accepts. Until then
the trust-boundary axiom `prometheus.Register.wp_proof` (item 4), which, once the glue was in place,
claimed a triple of the glue's code for every semantics, the model's names included.
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.Register
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.promreg.Registry__Register

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode
open _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.lib

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.prometheus.client_golang.prometheus.Assumptions]
variable [promreg_sem : promreg.Assumptions]

theorem prometheus.Register.wp_proof
    (hReg : promreg.Registry.Register.spec (GF := GF) (hG := hG)) :
    prometheus.Register.spec (GF := GF) (hG := hG) := by
  intro c ds Hd Hok
  wp_start as Htoks
  ihave #Hp : (github_com.prometheus.client_golang.prometheus.promInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold github_com.prometheus.client_golang.prometheus.promInit at Hp
  icases Hp with ⟨%l, #Hl, #Hreg⟩
  ihave #Hpr : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.promreg $$ []
  · iPkgInit
  try simp only [prometheus.model_Collector_eq, prometheus.model_defaultRegistry_eq]
  wp_auto
  wp_apply (Hd GF) as %sd Hsd
  try wp_auto
  wp_apply (hReg prometheus.descId l sd (DFrac.own 1) ds Hok) $$ [Hsd Htoks] as -
  · iframe #; iframe
  try wp_auto
  iapply HΦ
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial

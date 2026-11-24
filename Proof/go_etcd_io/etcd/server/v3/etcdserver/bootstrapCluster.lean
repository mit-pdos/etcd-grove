/-
Proof of `bootstrapCluster.spec` (claim #34, stage 2, 2026-11-25; `bootstrap.go:330-345` at the etcd
pin): the switch's second case (`bwal == nil && cfg.NewCluster`, the first is excluded by
`bootCfgFresh`'s `NewCluster`), `bootstrapNewClusterNoWAL`'s spec, then the error check.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapCluster
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapNewClusterNoWAL

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem bootstrapCluster.wp_proof
    (hNew : bootstrapNewClusterNoWAL.spec (GF := GF) (hG := hG)) :
    bootstrapCluster.spec (GF := GF) (hG := hG) := by
  intro cfg U H prt Hfresh HU Hfips HiOk
  have hnc : cfg.NewCluster' = true := Hfresh.1
  wp_start as ⟨#Hzlg, #Hro, Hrt⟩
  wp_auto
  rw [show decide (true = !cfg.NewCluster') = false by simp [hnc]]
  try wp_auto
  wp_apply (hNew cfg U H prt Hfresh HU Hfips HiOk) $$ [Hrt] as %c %err Hres
  · iframe #; iframe Hrt
  try wp_auto
  icases Hres with (%Hne | ⟨%Heq, Hok⟩)
  · obtain ⟨ei, rfl⟩ : ∃ ei, err = GoInterface.ok ei := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok ei => exact ⟨ei, rfl⟩
    try wp_auto
    iapply HΦ
    ileft; ipureintro; exact Hne
  subst Heq
  try wp_auto
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  iexact Hok

end proof

end EtcdGrove
end Perennial

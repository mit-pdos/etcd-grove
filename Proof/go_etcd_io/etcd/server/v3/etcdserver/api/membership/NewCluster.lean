/-
Proof of `membership.NewCluster.spec` (claim #34, stage 2, 2026-11-25): the options, the struct
literal (two fresh maps, a fresh `DowngradeInfo`), split field by field.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.NewCluster
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.newClusterOpts

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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem membership.NewCluster.wp_proof
    (hOpts : membership.newClusterOpts.spec (GF := GF) (hG := hG)) :
    membership.NewCluster.spec (GF := GF) (hG := hG) := by
  intro lg opts f ml
  wp_start as ⟨#Hlg, #Hopts, #Hf⟩
  ihave %Hlgnn := zapLoggerOk_ne_null lg $$ Hlg
  try wp_auto
  simp only [Hlgnn, decide_false, Bool.false_eq_true, ↓reduceIte]
  try wp_auto
  wp_apply hOpts opts f ml $$ [] as %co Hml
  · iframe #
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %mp Hmp
  wp_apply (wp_map_make1 (K := w64) (V := Bool)) as %rp Hrp
  try wp_auto
  irename «$r0» => Hc
  generalize «$r0_ptr» = c at *
  ihave %Hcnn := typedPointsto_not_null $$ Hc
  iStructNamed Hc
  iapply HΦ
  isplitr
  · ipureintro; exact Hcnn
  unfold membership.clusterOwned membership.memAt membership.memDom
  iexists _, rp, _
  iframe
  try iframe #
  isplitr
  · ipureintro; exact ⟨fun _ => rfl, by simp only [GMap.map_size_empty]⟩
  iapply BigSepM.bigSepM_empty.2; itrivial

end proof

end EtcdGrove
end Perennial

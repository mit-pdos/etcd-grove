module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchOptions
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.matchOpt
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.predicate

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem watchOptions.wp_proof
    (wp_matchOpt : matchOpt.spec (GF := GF) (hG := hG))
    (wp_predicate : predicate.spec (GF := GF) (hG := hG)) :
    watchOptions.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start as -
  wp_auto
  wp_apply wp_predicate
  (try wp_auto)
  wp_apply wp_matchOpt
  (try wp_auto)
  wp_if_destruct
  · simp only [watchOptsV, predWV, predV]
    iapply HΦ
    rw [show sieOfL x = some false by simp [sieOfL, Hif]]
    simp only [sendInitOwn]; iexact f
  · have h1 := Hif
    wp_if_destruct
    · simp only [watchOptsV, predWV, predV]
      iapply HΦ
      rw [show sieOfL x = some true by simp [sieOfL, Hif]]
      simp only [sendInitOwn]; iexact t
    · simp only [watchOptsV, predWV, predV]
      iapply HΦ
      rw [show sieOfL x = none by simp only [sieOfL, if_neg Hif, if_neg h1]]
      simp only [sendInitOwn]; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial

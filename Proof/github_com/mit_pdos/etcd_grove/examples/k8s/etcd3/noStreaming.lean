/- Lean-first (no Rocq counterpart). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.noStreaming
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import GeneratedProof.k8s_io.component_base.featuregate

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem noStreaming.wp_proof : noStreaming.spec (GF := GF) (hG := hG) := by
  wp_start as -
  ihave #Pft : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.features $$ []
  · iPkgInit
  ihave #Hft : (k8s_io.apiserver.pkg.storage.etcd3.featuresInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pft
  icases Hft with ⟨%g, #Hg, #Hgate⟩
  ihave #Puf : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.util.feature $$ []
  · iPkgInit
  ihave #Hfi : (k8s_io.apiserver.pkg.storage.etcd3.featureInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Puf
  icases Hfi with ⟨%g', #Hm, #Hd⟩
  icombine Hd Hg gives %Heq
  cases Heq
  iunfold EtcdGrove.k8sfeature.featureGateOk at Hgate
  icases Hgate with ⟨-, #Hset⟩
  wp_auto
  rw [show go!"EtcdRangeStream=false" = go!"EtcdRangeStream" ++ go!"=false" from rfl]
  wp_apply Hset as %err Herr
  · ipureintro; simp [EtcdGrove.k8sfeature.k8sQueriedFeatures]
  icases Herr with (⟨%Hn, #Hoff⟩ | %Hn)
  · subst Hn
    wp_auto
    iapply HΦ
    simp only [ite_true]
    iunfold rangeStreamOff
    iexists g
    iframe #
  · cases err with
    | nil => exact absurd rfl Hn
    | ok i => ?_
    wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ite_false]
    ipureintro; trivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial

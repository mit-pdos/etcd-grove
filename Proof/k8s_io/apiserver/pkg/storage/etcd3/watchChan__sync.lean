/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/watchChan__sync.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__sync
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.watchChan__syncPaginated
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem watchChan.sync.wp_proof
    (wp_syncPaginated : watchChan.syncPaginated.spec (GF := GF) (hG := hG)) :
    watchChan.sync.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ _ wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp recur r0 lbf q
    hQ hH hR hf hle
  wp_start as ⟨Hlt, #Hoff, #Hst, #Hsw, #Hwc, Hir, #Hra, #Hre, Hps, Hpe⟩
  ihave #Pft : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.features $$ []
  · iPkgInit
  ihave #Hft : (k8s_io.apiserver.pkg.storage.etcd3.featuresInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Pft
  icases Hft with ⟨%g, #Hg, #Hgate⟩
  iunfold EtcdGrove.k8sfeature.featureGateOk at Hgate
  icases Hgate with ⟨#Hen, -⟩
  iunfold rangeStreamOff at Hoff
  icases Hoff with ⟨%g', #Hg', #Hoff⟩
  ihave %Hag := typedPointsto_agree_wand _ _ _ _ _ $$ Hg Hg'
  cases Hag
  ihave #Hwc' := Hwc
  iunfold kWcProd at Hwc'
  icases Hwc' with ⟨%wp, %chI, %chR, %lg, %cf, %rse, %γc, #Hfw, -, -, #Hfr, -⟩
  wp_auto
  cases recur
  · wp_auto
    wp_apply (wp_syncPaginated Obj wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp false r0 lbf q
      hQ hH hR hf hle) $$ [$Hlt $Hst $Hsw $Hwc $Hir $Hra $Hre $Hps $Hpe] as %err ⟨Hlt, Hpost⟩
    iapply HΦ; iframe Hlt; iexact Hpost
  · wp_auto
    wp_apply Hen as %b Hb
    · ipureintro; decide
    icases Hb with ⟨Hb, -⟩
    ihave %hb := Hb $$ Hoff
    subst hb
    wp_auto
    wp_apply (wp_syncPaginated Obj wc sp c W γk γ cd sel emp inS m Q procd alive ctx kp true r0 lbf q
      hQ hH hR hf hle) $$ [$Hlt $Hst $Hsw $Hwc $Hir $Hra $Hre $Hps $Hpe] as %err ⟨Hlt, Hpost⟩
    iapply HΦ; iframe Hlt; iexact Hpost

end proof

end k8s
end EtcdGrove
end Perennial

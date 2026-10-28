/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/RealPodControl__createPods.lean`, over gap D2's body
hypothesis (`RealPodControl__createPods_body.lean`). Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.RealPodControl__createPods
public import Spec.k8s_io.kubernetes.pkg.controller.RealPodControl__createPods_body
public import Spec.fmt.Errorf
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Clientset__CoreV1
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.coreV1__Pods
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.podClient__Create
public import Spec.k8s_io.apimachinery.pkg.api.errors.HasStatusCause
public import Spec.k8s_io.klog.v2.FromContext
public import Spec.k8s_io.klog.v2.KObj
public import Spec.k8s_io.apimachinery.pkg.api.meta.Accessor
public import Spec.github_com.go_logr.logr.Logger__V_ptr
public import Spec.github_com.go_logr.logr.Logger__Info
public import Spec.github_com.go_logr.logr.Logger__Error_ptr
public import Spec.k8s_io.apimachinery.pkg.apis.meta.v1.ObjectMeta__GetName
public import Proof.k8s_io.kubernetes.pkg.controller.PodLens

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode apimodel k8s_io.kubernetes.pkg.controller

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]
variable [api_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.apimodel.Assumptions]

theorem RealPodControl.createPods.wp_proof
    (h_body : RealPodControl.createPods_body.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_CoreV1 : apimodel.Clientset.CoreV1.spec (GF := GF) (hG := hG))
    (wp_Pods : apimodel.coreV1.Pods.spec (GF := GF) (hG := hG))
    (wp_Create : apimodel.podClient.Create.spec (GF := GF) (hG := hG))
    (wp_HasStatusCause : apierrors.HasStatusCause.spec (GF := GF) (hG := hG))
    (wp_FromContext : klog.FromContext.spec (GF := GF) (hG := hG))
    (wp_Accessor : apimeta.Accessor.spec (GF := GF) (hG := hG))
    (wp_GetName : metav1.ObjectMeta.GetName.spec (GF := GF) (hG := hG))
    (wp_KObj : klog.KObj.spec (GF := GF) (hG := hG))
    (wp_V : logr.Logger.V_ptr.spec (GF := GF) (hG := hG))
    (wp_Info : logr.Logger.Info.spec (GF := GF) (hG := hG)) :
    RealPodControl.createPods.spec (GF := GF) (hG := hG) := by
  intro deps r γ cfg ctx ns p d l dd cref Ψ Ψ'
  haveI := h_body.1
  wp_start as H
  icases H with ⟨%Hctx, #Hcl, #Hrec, Hds, Hp, HAU, Hon⟩
  wp_auto
  icases podAt_labels p _ d $$ Hp with ⟨%m, Hm, Hmd, Hpback⟩
  wp_auto
  -- the labels: none, or a map `M`; `len` is `0` exactly when there is none
  cases hlab : d.ObjectMeta'.Labels' with
  | none =>
    ihave %hm := ownMapD_none m _ none rfl $$ Hmd
    subst hm
    wp_auto
    ihave Hsl := ownSlice_nil (V := GoInterface) (GF := GF) (DFrac.own 1)
    wp_apply (wp_Errorf _ slice.nil ([] : List GoInterface) (DFrac.own 1)) $$
      [Hsl] as %e ⟨-, -⟩
    · isplitr
      · iexact Hsl
      unfold fmt.argsOk; itrivial
    iapply HΦ
    isplitl [Hm Hmd Hpback]
    · iapply Hpback $$ Hm Hmd
    iright; iright
    iframe
    ipureintro
    exact ⟨by simp, rfl⟩
  | some M =>
    ihave Hmd := (ownMapD_some m _ (some M) M rfl).1 $$ Hmd
    wp_apply (wp_map_len_lt m M (DFrac.own 1)) $$ [Hmd] as ⟨Hmd, %hlt⟩
    · iexact Hmd
    wp_if_destruct
    · -- empty labels: refused
      have hz : GMap.size M = 0 := by
        have h2 := congrArg BitVec.toNat Hif
        simp only [W64, BitVec.toNat_ofInt] at h2
        omega
      have hM : M = ∅ := GMap.map_size_empty_inv M hz
      ihave Hsl := ownSlice_nil (V := GoInterface) (GF := GF) (DFrac.own 1)
      wp_apply (wp_Errorf _ slice.nil ([] : List GoInterface) (DFrac.own 1)) $$
        [Hsl] as %e ⟨-, -⟩
      · isplitr
        · iexact Hsl
        unfold fmt.argsOk; itrivial
      iapply HΦ
      isplitl [Hm Hmd Hpback]
      · iapply Hpback $$ Hm
        iapply (ownMapD_some m _ (some M) M rfl).2 $$ Hmd
      iright; iright
      iframe
      ipureintro
      exact ⟨by simp, by simp [hM]⟩
    · ihave Hp := Hpback $$ Hm [Hmd]
      · iapply (ownMapD_some m _ (some M) M rfl).2 $$ Hmd
      iunfold clientIs at Hcl
      icases Hcl with ⟨%c, %hkc, #Hcs, #Hapi⟩
      rw [hkc]
      wp_auto
      wp_apply (wp_CoreV1 c γ cfg false) $$ [] as %x Hx
      · iexact Hcs
      iunfold isCoreV1 at Hx
      icases Hx with ⟨%lc, %hx, Hlc⟩
      subst hx
      wp_auto
      wp_apply (wp_Pods lc γ cfg false ns) $$ [Hlc] as %y Hy
      · iexact Hlc
      iunfold isPodClient at Hy
      icases Hy with ⟨%lp, %hy, Hlp⟩
      subst hy
      wp_auto
      wp_bind
      iapply (wp_Create lp γ cfg ns false ctx p (DFrac.own 1) d (zero_val _)) $$ [Hlp Hp]
      · simp only [objPtrAt]
        isplitr
        · iexact Hapi
        iframe
      inext
      rw [Iris.Std.LawfulSet.diff_empty]
      iunfold createAU at HAU
      imod HAU with ⟨%σ, Hσ, HAUcl⟩
      imodintro
      iexists σ
      iframe Hσ
      iintro %σ' %oc ⟨Hσ', %Hout⟩
      imod HAUcl $$ %σ' %oc %Hout Hσ' with HΨ
      imodintro
      iintro %q %err ⟨Hp, Hret⟩
      wp_auto
      cases oc with
      | error e =>
        iunfold writeRet at Hret
        icases Hret with ⟨%hq, Herr⟩
        iunfold errIs at Herr
        icases Herr with ⟨%sp, %st, %herr, #Hsp, %hst⟩
        subst herr
        wp_auto
        wp_apply (wp_HasStatusCause _ _) as %b _
        iunfold recorderOk at Hrec
        icases Hrec with ⟨%i, %hi, #HEv⟩
        cases b
        · simp only [Bool.not_false]
          wp_auto
          wp_apply wp_slice_literal (V := GoInterface)
            [interface.mkOk (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) #sp]
          isplitr
          · ipureintro; rfl
          iintro %asl ⟨Hasl, -⟩
          wp_auto
          rw [hi]
          dsimp only
          wp_bind
          iapply HEv $$ Hasl
          inext
          iintro Hasl
          wp_auto
          iapply HΦ
          isplitl [Hp]
          · iunfold objPtrAt at Hp; iexact Hp
          iright; ileft
          isplitr
          · ipureintro; simp [interface.mkOk]
          iexists _
          iframe HΨ
          ipureintro; trivial
        · simp only [Bool.not_true]
          wp_auto
          iapply HΦ
          isplitl [Hp]
          · iunfold objPtrAt at Hp; iexact Hp
          iright; ileft
          isplitr
          · ipureintro; simp [interface.mkOk]
          iexists _
          iframe HΨ
          ipureintro; trivial
      | ok we =>
        obtain ⟨w, o⟩ := we
        obtain ⟨hw, dp, ho⟩ := CreateOut_ok_pod Hout
        subst hw ho
        iunfold writeRet at Hret
        icases Hret with (⟨%he, Hq⟩ | ⟨%hamb, Herr⟩)
        · subst he
          wp_auto
          wp_apply (wp_FromContext ctx) as %lg _
          · ipureintro; exact Hctx
          iunfold onWriteOk at Hon
          icases Hon with ⟨%hnn, Hcb⟩
          iunfold objPtrAt at Hq
          simp only [hnn, decide_false, Bool.not_false]
          wp_auto
          wp_bind
          iapply Hcb $$ Hq HΨ
          inext
          iintro Hq HΨ'
          wp_pures
          wp_auto
          have hA := wp_Accessor .daemonSets l
          simp only [apimeta.apiPtrTy] at hA
          wp_apply hA
          wp_apply (dsAt_GetName wp_GetName l _ dd) $$ [Hds] as Hds
          · iexact Hds
          ihave Hqo : objAt (interface.mkOk (go.GoType.PointerType k8s_io.api.core.v1.Pod.ty) #q)
            (DFrac.own 1) (.pod dp) $$ [Hq]
          · iunfold objAt; iexists q; iframe; ipureintro; rfl
          wp_apply (wp_KObj _ _ _) $$ [Hqo] as %oref Hqo
          · iexact Hqo
          wp_apply wp_slice_literal (V := GoInterface)
            [interface.mkOk go.string #go!"controller", interface.mkOk go.string #dd.ObjectMeta'.Name',
              interface.mkOk go.string #go!"pod", interface.mkOk k8s_io.klog.v2.ObjectRef.ty #oref]
          isplitr
          · ipureintro; rfl
          iintro %ksl ⟨Hksl, -⟩
          wp_auto
          wp_apply (wp_V logger_ptr lg (DFrac.own 1) (W64 4)) $$ [logger] as %lg4 logger
          · iexact logger
          wp_apply (wp_Info lg4 _ _ (DFrac.own 1) _) $$ [Hksl] as Hksl
          · iexact Hksl
          wp_auto
          iunfold objAt at Hqo
          icases Hqo with ⟨%q', %hq', Hq⟩
          have hqq : q' = q := by
            simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at hq'
            exact (go.intoVal_inj hq').symm
          subst hqq
          icases podAt_name q' _ dp $$ Hq with ⟨Hname, Hqback⟩
          wp_auto
          wp_apply wp_slice_literal (V := GoInterface) [interface.mkOk go.string #dp.ObjectMeta'.Name']
          isplitr
          · ipureintro; rfl
          iintro %esl ⟨Hesl, -⟩
          wp_auto
          iunfold recorderOk at Hrec
          icases Hrec with ⟨%i, %hi, #HEv⟩
          rw [hi]
          dsimp only
          wp_bind
          iapply HEv $$ Hesl
          inext
          iintro Hesl
          wp_auto
          iapply HΦ
          isplitl [Hp]
          · iunfold objPtrAt at Hp; iexact Hp
          ileft
          isplitr
          · ipureintro; rfl
          iexists dp
          iexact HΨ'
        · iunfold errIs at Herr
          icases Herr with ⟨%sp, %st, %herr, #Hsp, %hst⟩
          subst herr
          wp_auto
          wp_apply (wp_HasStatusCause _ _) as %b _
          iunfold recorderOk at Hrec
          icases Hrec with ⟨%i, %hi, #HEv⟩
          cases b
          · simp only [Bool.not_false]
            wp_auto
            wp_apply wp_slice_literal (V := GoInterface)
              [interface.mkOk (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) #sp]
            isplitr
            · ipureintro; rfl
            iintro %asl ⟨Hasl, -⟩
            wp_auto
            rw [hi]
            dsimp only
            wp_bind
            iapply HEv $$ Hasl
            inext
            iintro Hasl
            wp_auto
            iapply HΦ
            isplitl [Hp]
            · iunfold objPtrAt at Hp; iexact Hp
            iright; ileft
            isplitr
            · ipureintro; simp [interface.mkOk]
            iexists _
            iframe HΨ
            ipureintro; exact ⟨rfl, hamb.2.1⟩
          · simp only [Bool.not_true]
            wp_auto
            iapply HΦ
            isplitl [Hp]
            · iunfold objPtrAt at Hp; iexact Hp
            iright; ileft
            isplitr
            · ipureintro; simp [interface.mkOk]
            iexists _
            iframe HΨ
            ipureintro; exact ⟨rfl, hamb.2.1⟩

end proof

end dsctl
end EtcdGrove
end Perennial

/-
Proof of `Spec/k8s_io/client_go/tools/cache/sharedIndexInformer__OnUpdate.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.sharedIndexInformer__OnUpdate
public import Spec.k8s_io.client_go.tools.cache.sharedProcessor__distribute

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem sharedIndexInformer.OnUpdate.wp_proof
    (wp_dist : sharedProcessor.distribute.spec (GF := GF) (hG := hG)) :
    sharedIndexInformer.OnUpdate.spec (GF := GF) (hG := hG) := by
  intro s p γp γe evs OK old new Hbound
  wp_start as ⟨#Hs, #Hacc, #Hold, #Hnew, HH⟩
  iunfold isSII at Hs
  icases Hs with ⟨#Hp, ⟨%d, #Hd, #Hmd⟩, #Hproc⟩
  iunfold mdOk at Hmd
  icases Hmd with ⟨%di, %Hdi, #Hadd⟩
  subst Hdi
  iunfold infH at HH
  icases HH with ⟨Hsend, Hrd, Hauth⟩
  iunfold accRet at Hacc
  wp_auto
  -- `isSync`: whether the two objects' resource versions agree (it only selects the syncing
  -- listeners, which are all of them)
  wp_bind (Let "__p" _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ new_ptr ↦ new ∗ old_ptr ↦ old ∗
      ∃ isSync : Bool, isSync_ptr ↦ isSync)))
    $$ [isSync new old]
  · ihave #Hn := Hacc $$ %new
    wp_bind (App (Val #(functions k8s_io.apimachinery.pkg.api.«meta».Accessor [])) (Val #new))
    iapply Hn $$ [$Hnew]
    inext
    iintro %m %err Hm
    icases Hm with (%herr | ⟨%herr, %rv, #Hrv⟩)
    · cases err with
      | nil => exact absurd rfl herr
      | ok ei =>
        wp_auto
        iframe; ipureintro; rfl
    · subst herr
      wp_auto
      ihave #Ho := Hacc $$ %old
      wp_bind (App (Val #(functions k8s_io.apimachinery.pkg.api.«meta».Accessor [])) (Val #old))
      iapply Ho $$ [$Hold]
      inext
      iintro %m2 %err2 Hm2
      icases Hm2 with (%herr2 | ⟨%herr2, %rv2, #Hrv2⟩)
      · cases err2 with
        | nil => exact absurd rfl herr2
        | ok ei =>
          wp_auto
          iframe; ipureintro; rfl
      · subst herr2
        wp_auto
        cases m with
        | nil => iunfold getRVOk at Hrv; icases Hrv with ⟨⟩
        | ok mi =>
        cases m2 with
        | nil => iunfold getRVOk at Hrv2; icases Hrv2 with ⟨⟩
        | ok mi2 =>
        iunfold getRVOk at Hrv Hrv2
        wp_auto
        wp_bind (App (Val #(methods mi.ty go!"GetResourceVersion" mi.v)) (Val #()))
        iapply Hrv
        · itrivial
        inext
        iintro -
        wp_auto
        wp_bind (App (Val #(methods mi2.ty go!"GetResourceVersion" mi2.v)) (Val #()))
        iapply Hrv2
        · itrivial
        inext
        iintro -
        wp_auto
        iframe; ipureintro; rfl
  iintro %v ⟨%hv, new, old, %isSync, isSync⟩
  subst hv
  wp_auto
  ihave #H1 := Hadd $$ %new
  wp_bind (App (Val #(methods di.ty go!"AddObject" di.v)) (Val #new))
  iapply H1
  · itrivial
  inext
  iintro -
  wp_auto
  imod (monoListAuthOwn_update_app (l := evs.map notifOf) [notifOf (Ev.update old new)]) $$ Hauth
    with ⟨Hauth, #Hlb⟩
  ihave #HQ : notifQ γe evs.length (Ev.update old new) $$ []
  · iunfold notifQ
    iapply (monoListIdxOwn_get (l := evs.map notifOf ++ [notifOf (Ev.update old new)]) evs.length
      (notifOf (Ev.update old new)) (by simp)) $$ Hlb
  rw [show interface.mkOk updateNotification.ty #(updateNotification.mk old new) =
    notifOf (Ev.update old new) from rfl]
  wp_apply (wp_dist p γp (notifQ γe) evs (Ev.update old new) isSync Hbound)
    $$ [$Hpkg $Hproc $Hrd $Hsend $HQ] as ⟨Hrd, Hsend⟩
  iapply HΦ
  iunfold infH
  iframe
  simp only [List.map_append, List.map_cons, List.map_nil]
  iexact Hauth

end proof

end cache
end EtcdGrove
end Perennial

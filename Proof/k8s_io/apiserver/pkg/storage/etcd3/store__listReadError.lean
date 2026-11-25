/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__listReadError.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__listReadError
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.interpretListError
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__GetCurrentResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.NewTooLargeResourceVersionError
public import Spec.errors.IsStatusErr
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
variable [errors_sem : _root_.Perennial.errors.Assumptions]

theorem store.listReadError.wp_proof
    (wp_interpretListError : interpretListError.spec (GF := GF) (hG := hG))
    (wp_GetCRV : store.GetCurrentResourceVersion.spec (GF := GF) (hG := hG))
    (wp_TooLarge : storage.NewTooLargeResourceVersionError.spec (GF := GF) (hG := hG))
    (wp_Is : errors.IsStatusErr.spec (GF := GF) (hG := hG)) :
    store.listReadError.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c ci cd err withRev ck kp Q hk
  obtain ⟨k, hk, hkl⟩ := hk
  wp_start as ⟨Hlt, #Hst, #Hctx, #Hce, #Herr⟩
  ihave #Prt : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Prt
  icases Hri with ⟨⟨%eFR, #HeFR, #HdFR, %HtFR⟩, -⟩
  obtain ⟨-, x, hx⟩ := HtFR
  iunfold readErrIs at Herr
  icases Herr with ⟨#Hke, %d, #Hd, #Hfut⟩
  ihave #Hke' := Hke
  iunfold kClientErr at Hke'
  icases Hke' with ⟨%hce, #Hse, -⟩
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  wp_auto
  wp_apply (wp_Is err (GoInterface.ok eFR) (some (d, _)) (Or.inl ⟨x, hx⟩)) $$ [$Hse] as %b %hb
  · iapply go_etcd_io.etcd.cache.v3.isDescs_some $$ Hd HdFR
  cases b
  · -- not a future revision: `interpretListError`
    wp_auto
    wp_apply (wp_interpretListError Obj c err false ck kp (by simp)) $$ [$Hke] as %e #He
    iapply HΦ
    iframe Hlt
    iright
    iapply listErrF_listErr $$ He
  · -- a future revision: the state below `withRev`, and the too-large error
    ihave %hF := go_etcd_io.etcd.cache.v3.descIs_is_etcdError _ x _ (Or.inl hx) $$ HdFR
    ihave %hd : ⌜d = go_etcd_io.etcd.cache.v3.futureRevDesc⌝ $$ []
    · rcases (hb rfl).1 _ _ rfl with h | h
      · ihave %h2 := go_etcd_io.etcd.cache.v3.descIs_is_etcdError _ x _ (Or.inl (h.trans hx)) $$ Hd
        ipureintro; rw [h2, hF]
      · ipureintro; exact h
    ihave #HQ := Hfut $$ %hd %((hb rfl).2 ⟨x, hx⟩)
    wp_auto
    wp_apply (wp_GetCRV Obj sp c ci cd k (fun _ _ _ => iprop(True)) hk hkl) $$ [$Hlt] as %n %e2 ⟨Hlt, -⟩
    · iframe #
      iintro %R %m
      imodintro
      imodintro
      refine BigAndL.bigAndL_intro fun _ _ _ => ?_
      iintro -
      ileft
      ipureintro; rfl
    cases e2
    all_goals
      wp_auto
      wp_apply wp_TooLarge as %e ⟨He0, -⟩
      ihave #He := He0 $$ %(by trivial)
      iapply HΦ
      iframe Hlt
      ileft
      iframe He HQ

end proof

end k8s
end EtcdGrove
end Perennial

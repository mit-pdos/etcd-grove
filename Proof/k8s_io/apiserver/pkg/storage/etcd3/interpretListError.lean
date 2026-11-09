/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/interpretListError.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.interpretListError
public import Spec.k8s_io.apimachinery.pkg.api.errors.NewResourceExpired

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
variable [rpc_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

theorem interpretListError.wp_proof
    (wp_NewResourceExpired : apierrors.NewResourceExpired.spec (GF := GF) (hG := hG)) :
    interpretListError.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ c err ck kp
  wp_start as #Herr
  ihave #Prt : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave Hri : (go_etcd_io.etcd.cache.v3.rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Prt
  icases Hri with ⟨-, ⟨%eCP, #HeCP, -, -, %HtCP⟩, -⟩
  obtain ⟨x, hx⟩ := HtCP
  ihave #Herr' := Herr
  iunfold kClientErr at Herr'
  icases Herr' with ⟨%hce, -, -⟩
  have hcp : eCP = ⟨go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty, #x⟩ := by
    cases eCP; simp only [interface.mkOk, GoInterface.ok.injEq] at hx; exact hx
  subst hcp
  obtain ⟨hne, hcl⟩ := hce
  cases err with
  | nil => exact absurd rfl hne
  | ok ii =>
  wp_auto
  -- the client's error as `listErr`
  have hret : ⊢ kClientErr (GF := GF) (GoInterface.ok ii) -∗ listErr c (GoInterface.ok ii) := by
    iintro #H
    iunfold listErr
    ileft
    iapply kClientErr_unkErr $$ H
  by_cases hty : ii.ty = go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty
  · have hv := (hcl.2 ii rfl).2
    unfold errors.AsTypeTyped at hv
    have hni : go.isInterfaceType (underlying go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) = false := by
      have hu : underlying go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty =
          go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.underlying := go.is_underlying
      rw [hu]
      simp only [go.isInterfaceType]
    rw [hni] at hv
    obtain ⟨y, hy⟩ := hv hty
    obtain ⟨t, v⟩ := ii
    simp only at hty hy
    subst hty hy
    simp only [↓reduceIte]
    wp_auto
    by_cases hc : y.code' = x.code'
    · rw [decide_eq_true hc]
      wp_auto
      by_cases hd : y.desc' = x.desc'
      · rw [decide_eq_true hd]
        wp_auto
        iapply wp_fupd
        wp_apply wp_NewResourceExpired as %p ⟨%st, Hp, %Hst⟩
        ipersist Hp
        imodintro
        iapply HΦ
        iunfold listErr
        iright
        iexists st
        isplitl
        · iunfold apierrors.apiErrAt
          iexists p
          isplitr
          · ipureintro; rfl
          iframe Hp
          iunfold apierrors.statusDetailsAt
          ileft
          ipureintro; exact ⟨Hst.2.2.2, rfl⟩
        · ipureintro; exact ⟨Hst.2.1, Hst.2.2.1⟩
      · rw [decide_eq_false hd]
        wp_auto
        iapply HΦ
        iapply hret $$ Herr
    · rw [decide_eq_false hc]
      wp_auto
      iapply HΦ
      iapply hret $$ Herr
  · simp only [hty, ↓reduceIte]
    wp_auto
    iapply HΦ
    iapply hret $$ Herr

end proof

end k8s
end EtcdGrove
end Perennial

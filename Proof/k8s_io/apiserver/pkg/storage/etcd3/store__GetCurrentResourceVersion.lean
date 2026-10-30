/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/etcd3/store__GetCurrentResourceVersion.lean`.
Lean-first (no Rocq counterpart).

As `store.Get`'s read: the prefix's key, the client's `Get` with the caller's updates, the
metrics; then the response's revision (the state's, below `2^63`: its `uint64` is the state's
revision), an error if it is `0`.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__GetCurrentResourceVersion
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__prepareKey
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordEtcdRequest
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__Get
public import Spec.fmt.Errorf
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.GetCurrentResourceVersion.wp_proof
    (wp_prepareKey : store.prepareKey.spec (GF := GF) (hG := hG))
    (wp_RecordEtcdRequest : metrics.RecordEtcdRequest.spec (GF := GF) (hG := hG))
    (wp_kGet : kubernetes.Client.Get.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    store.GetCurrentResourceVersion.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c ci cd k Q hk hkl
  wp_start as ⟨#Hst, #Hctx, #Hce, Hau⟩
  iunfold isStore at Hst
  icases Hst with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt, #Hkc,
    #Hcl, #Hone, #Hregs, #Hcon⟩
  ihave #Pme : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics $$ []
  · iPkgInit
  ihave #Pti : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Pku : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes $$ []
  · iPkgInit
  ihave #Pcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Pfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave Fgr' := Fgr
  iStructNamed Fgr'
  ihave Hkc' := Hkc
  iStructNamed Hkc'
  (try wp_auto)
  wp_apply wp_prepareKey sp c.resourcePrefix c.pathPrefix c.resourcePrefix false $$ [] as
    %pk %perr %Hpk
  · iframe #
  rw [hk] at Hpk
  obtain ⟨rfl, rfl⟩ := Hpk
  (try wp_auto)
  wp_apply _root_.Perennial.time.wp_Now as %t0 -
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty)
    (m := go!"Get")]
  wp_call
  (try wp_auto)
  wp_apply (wp_kGet (go_etcd_io.etcd.client.v3.kubernetes.Client.mk c.cl
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty) #c.kc))
      c.ms c.V ci cd (c.pathPrefix ++ k) (zero_val _) Q rfl) $$ [Hau]
    as %resp %gerr Hget
  · iframe #
    iexact Hau
  (try wp_auto)
  wp_apply wp_RecordEtcdRequest $$ []
  icases Hget with (⟨%Hgerr, %σ, #HQ, %Hσ, -⟩ | ⟨%Hgerr, -, -⟩)
  · -- the client read the state σ
    subst Hgerr
    obtain ⟨hrevσ, hb⟩ := Hσ
    (try wp_auto)
    rw [hrevσ]
    by_cases h0 : σ.rev = 0
    · have hz : (W64 (σ.rev : Int)) = W64 0 := by rw [h0]; rfl
      rw [hz]
      (try wp_auto)
      wp_apply (wp_Errorf _ slice.nil [] (DFrac.own 1)) $$ [] as %e -
      · iframe #
        isplitl
        · iapply ownSlice_nil
        unfold fmt.argsOk; itrivial
      (try wp_auto)
      iapply HΦ
      ileft
      ipureintro
      simp
    · have hnz : (W64 (σ.rev : Int)) ≠ W64 0 := by
        intro h; apply h0; have := congrArg (fun w : w64 => w.toNat) h; simp at this; omega
      (try wp_auto)
      simp only [hnz, decide_false]
      (try wp_auto)
      iapply HΦ
      iright
      isplitr
      · ipureintro; rfl
      iexists σ
      iframe HQ
      ipureintro
      constructor
      · exact hrevσ
      · omega
  · -- the client's error
    cases gerr with
    | nil => exact absurd rfl Hgerr
    | ok gi =>
    (try wp_auto)
    iapply HΦ
    ileft
    ipureintro
    exact Hgerr

end proof

end k8s
end EtcdGrove
end Perennial

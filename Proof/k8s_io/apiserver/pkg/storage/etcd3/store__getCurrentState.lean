/-
Lean-first (no Rocq counterpart).

The proof of `(*store).getCurrentState`: the closure's captured variables are never written, so
they are persisted, and each call reads through the client (`kubernetes.Client.Get`) and answers
by `stateFromEtcdResponse`, whose key-value decodes since the read state is the store's.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__getCurrentState
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__stateFromEtcdResponse
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.metrics.RecordEtcdRequest
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.Client__Get
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.getCurrentState.wp_proof
    (wp_stateFrom : store.stateFromEtcdResponse.spec (GF := GF) (hG := hG))
    (wp_RecordEtcdRequest : metrics.RecordEtcdRequest.spec (GF := GF) (hG := hG))
    (wp_kGet : kubernetes.Client.Get.spec (GF := GF) (hG := hG)) :
    store.getCurrentState.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ sp c ci cd verb key v p R hk hR
  wp_start as ⟨#Hst, #Hctx, #Hce, %Hv, #Hau⟩
  iapply wp_fupd
  (try wp_auto)
  ipersist s
  ipersist expectTransformOrDecodeError
  ipersist ignoreNotFound
  ipersist v
  ipersist key
  ipersist verb
  ipersist ctx
  rw [recv_eq_func_mk]
  imodintro
  iapply HΦ
  iunfold getStateOk
  imodintro
  iintro %Ψ HΨ
  ihave Hst' := Hst
  iunfold isStore at Hst'
  icases Hst' with ⟨%Hsp, #Fcl, #Fcodec, #Fvi, #Fti, #Fdi, #Fpp, #Frp, #Fgr, #Fmt, #Flt, %Hlt,
    #Hkc, #Hcl, #Hone, #Hregs, %Hwl, #Hcon⟩
  ihave #Pme : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3.metrics $$ []
  · iPkgInit
  ihave #Pti : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Pku : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes $$ []
  · iPkgInit
  ihave #Pcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave Hkc' := Hkc
  iStructNamed Hkc'
  wp_pure
  (try wp_auto)
  wp_apply _root_.Perennial.time.wp_Now as %t0 -
  (try wp_auto)
  rw [method_unfold (t := go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty)
    (m := go!"Get")]
  wp_call
  (try wp_auto)
  have hm : ∀ (i : Nat) (x : client.SrvAt GF), c.ms[i]? = some x →
      kvReadAu (GF := GF) x.γr.kv R ⊢ iprop(⌜R = fun _ => iprop(True)⌝ ∨ kvReadAu x.γr.kv R) :=
    fun _ _ _ => by iintro #h; iright; iexact h
  ihave #Hau' := (BigAndL.bigAndL_mono hm) $$ Hau
  wp_apply (wp_kGet (go_etcd_io.etcd.client.v3.kubernetes.Client.mk c.cl
      (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kubernetes.Client.ty) #c.kc))
      c.ms c.V ci cd key (zero_val _) R rfl) $$ []
    as %resp %gerr Hget
  · iframe #
  (try wp_auto)
  wp_apply wp_RecordEtcdRequest
  icases Hget with (⟨%Hgerr, %σ, #HR, %Hσ, #Hkv⟩ | ⟨%Hgerr, %Hgce, #Hgse⟩)
  · subst Hgerr
    obtain ⟨hrevσ, hb⟩ := Hσ
    ihave %Hwf := (hR σ) $$ HR
    have hdk : ∀ kv, mvcc.findKey key σ.kvs = some kv → ∃ o b, c.S.dec kv.value = some (o, b) :=
      fun kv hkv => c.dec_of_wf σ Hwf key hk kv hkv
    (try wp_auto)
    wp_apply (wp_stateFrom Obj sp c (GoInterface.ok ci) resp.KV' (mvcc.findKey key σ.kvs)
        resp.Revision' key v p hdk) $$ [] as %st %err Hres
    · iframe #
      ipureintro; exact Hv
    (try wp_auto)
    iapply HΨ
    iright
    iexists σ
    iframe HR
    unfold stAt
    rw [← hrevσ]
    iexact Hres
  · cases gerr with
    | nil => exact absurd rfl Hgerr
    | ok ei =>
      (try wp_auto)
      iapply HΨ
      ileft
      ipureintro; nofun

end proof

end k8s
end EtcdGrove
end Perennial

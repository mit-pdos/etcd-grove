/-
Proof of `Spec/go_etcd_io/etcd/client/v3/kv__Get.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kv__Get
public import Spec.go_etcd_io.etcd.client.v3.kv__Do
public import Proof.go_etcd_io.etcd.client.v3.OpGetRes
public import Spec.go_etcd_io.etcd.client.v3.ContextError
public import Proof.go_etcd_io.etcd.client.v3.KVMembers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `kv.Get` for any spec registered for `Range` (`kv.Get.specG`): `OpGet`, then `kv.Do` at the
spec, the other two methods' specs unused (`doRunGen`'s range case). -/
theorem kv.Get.wp_generic
    (wp_NewOp : NewOp.spec (GF := GF) (hG := hG))
    (wp_Do : kv.Do.specG (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Get.specG (GF := GF) (hG := hG) := by
  intro api conn addr ci cd key sl gs R Sr Qr
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hopts, HR, #Hsn, %Hnp, #Hrpc, #Hrun⟩
  obtain ⟨Hnp, Ht⟩ := Hnp
  wp_auto
  wp_apply (opGet_res wp_NewOp key sl gs R) $$ [$HR] as %opv ⟨#Hat, HR⟩
  · iframe #; ipureintro; exact Hnp
  wp_apply wp_Do api conn addr ci cd opv (opGetModel key gs) (fun _ _ _ => iprop(False))
      (fun _ => iprop(True)) Sr Qr (fun _ _ _ => iprop(False)) (fun _ => iprop(True)) $$ []
    as %r %err Hout
  · iframe #
    unfold doRunGen
    ileft
    iframe #
    ipureintro; exact Ht
  ihave Hout' : rangeCallOut Qr r.get' err
      $$ [Hout]
  · have Heq : doOut (opGetModel key gs) (fun _ => iprop(True)) Qr (fun _ => iprop(True)) r err =
        rangeCallOut Qr r.get' err := by
      unfold doOut; rw [Ht]; simp only [↓reduceIte]
    rw [← Heq]; iexact Hout
  iunfold rangeCallOut at Hout'
  icases Hout' with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · subst Herr
    ihave #Hse0 := go_etcd_io.etcd.cache.v3.statusErrOk_nil (GF := GF)
    wp_apply wp_ContextError ci cd GoInterface.nil $$ [$Hse0] as %err' ⟨%Herr', -⟩
    · iframe #; ipureintro; exact fun h => (h rfl).elim
    obtain ⟨H1, -⟩ := Herr'
    rw [H1 rfl]
    iapply HΦ
    iframe HR
    unfold rangeCallOut
    ileft
    iframe
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    wp_apply wp_ContextError ci cd err $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
    · iframe #; ipureintro; exact fun _ => Hce'
    ihave #Hcl' := Hclw $$ Hcl
    iapply HΦ
    iframe HR
    unfold rangeCallOut
    iright
    iframe #
    ipureintro
    exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩


/-- `kv.Get` on a `*kv` of the members (`kv.Get.specM`, D44): `kv.Get.wp_generic` at the members'
plain spec at every metadata (`GrpcSpec.md (kvRangeSpec ms)`; `kvRegs_rpcRange`, `rangeSpec_of`). -/
theorem kv.Get.wp_members
    (wp_Get : kv.Get.specG (GF := GF) (hG := hG)) :
    kv.Get.specM (GF := GF) (hG := hG) := by
  intro api ms ci cd key sl gs R c F Q
  iintro %Φ ⟨#Pc, #Hkv, #Hctx, #Hce, #Hopts, HR, #Hsn, %Hnp, #Hk, #Hrun⟩ HΦ
  iunfold isKV at Hkv
  icases Hkv with ⟨#Hobj, #Hregs⟩
  icases (kvObjAt_conn api (ms.map SrvAt.addr)).1 $$ Hobj with ⟨%conn, #Hobj⟩
  iapply (wp_Get api conn (ms.map SrvAt.addr) ci cd key sl gs R (GrpcSpec.md (kvRangeSpec ms))
    (rangeAns ms c F (rangeWireOf (opGetModel key gs)) Q)) $$ [HR] HΦ
  iframe #
  iframe HR
  isplitl []
  · ipureintro; exact Hnp
  isplitl []
  · iapply (isGrpcRpcs_md _ _ _).1; iapply (kvRegs_rpcRange ms) $$ Hregs
  imodintro
  inext
  iapply (attemptPre_md conn (GoInterface.ok ci) (kvRangeSpec ms) (rangeWireOf (opGetModel key gs))
    (rangeAns ms c F (rangeWireOf (opGetModel key gs)) Q))
  iapply (rangeSpec_of ms c F (rangeWireOf (opGetModel key gs)) Q)
  iframe Hk Hrun

theorem kv.Get.wp_proof
    (wp_NewOp : NewOp.spec (GF := GF) (hG := hG))
    (wp_Do : kv.Do.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Get.spec (GF := GF) (hG := hG) := by
  intro api γ dup ci cd key sl gs R Q
  wp_start as ⟨#Hkv, #Hctx, #Hce, #Hopts, HR, #Hsn, %Hnp, #Hrun⟩
  obtain ⟨Hnp, Ht⟩ := Hnp
  wp_auto
  wp_apply (opGet_res wp_NewOp key sl gs R) $$ [$HR] as %opv ⟨#Hat, HR⟩
  · iframe #; ipureintro; exact Hnp
  wp_apply wp_Do api γ dup ci cd opv (opGetModel key gs) Q $$ []
    as %r %err Hout
  · iframe #
    unfold doRunOk
    ileft
    iframe #
    ipureintro; exact Ht
  ihave Hout' : rangeCallOut (rangeStOk (rangeWireOf (opGetModel key gs)) Q) r.get' err
      $$ [Hout]
  · have Heq : doOut (opGetModel key gs) (putStOk (putWireOf (opGetModel key gs)) Q)
        (rangeStOk (rangeWireOf (opGetModel key gs)) Q)
        (delStOk (deleteWireOf (opGetModel key gs)) Q) r err =
        rangeCallOut (rangeStOk (rangeWireOf (opGetModel key gs)) Q) r.get' err := by
      unfold doOut; rw [Ht]; simp only [↓reduceIte]
    rw [← Heq]; iexact Hout
  iunfold rangeCallOut at Hout'
  icases Hout' with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · subst Herr
    ihave #Hse0 := go_etcd_io.etcd.cache.v3.statusErrOk_nil (GF := GF)
    wp_apply wp_ContextError ci cd GoInterface.nil $$ [$Hse0] as %err' ⟨%Herr', -⟩
    · iframe #; ipureintro; exact fun h => (h rfl).elim
    obtain ⟨H1, -⟩ := Herr'
    rw [H1 rfl]
    iapply HΦ
    iframe HR
    iapply rangeCallOut_st
    unfold rangeCallOut
    ileft
    iframe
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    wp_apply wp_ContextError ci cd err $$ [$Hse] as %err' ⟨%Herr', #Hse', #Hclw⟩
    · iframe #; ipureintro; exact fun _ => Hce'
    ihave #Hcl' := Hclw $$ Hcl
    iapply HΦ
    iframe HR
    iapply rangeCallOut_st
    unfold rangeCallOut
    iright
    iframe #
    ipureintro
    exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩

end proof

end EtcdGrove
end Perennial

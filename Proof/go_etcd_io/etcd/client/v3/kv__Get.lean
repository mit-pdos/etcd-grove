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
  intro api conn addr ci om cd key sl gs R Sr Qr Ψr
  wp_start as ⟨Hlt, #Hkv, #Hom, #Hctx, #Hce, #Hopts, HR, #Hsn, %Hnp, #Hrpc, #Hrun, %Hsz⟩
  obtain ⟨Hnp, Ht⟩ := Hnp
  wp_auto
  wp_apply (opGet_res wp_NewOp key sl gs R) $$ [$HR] as %opv ⟨#Hat, HR⟩
  · iframe #; ipureintro; exact Hnp
  wp_apply wp_Do api conn addr ci om cd opv (opGetModel key gs) (fun _ _ _ _ => iprop(False))
      (fun _ => iprop(True)) Sr Qr (fun _ _ _ _ => iprop(False)) (fun _ => iprop(True)) Ψr $$ []
    as %r %err ⟨Heo, Hout⟩
  · iframe #
    isplitl []; rotate_left
    · ipureintro; exact Hsz
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
    ihave ⟨%mC, #HmC⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hse0
    wp_apply wp_ContextError ci cd GoInterface.nil mC $$ [$Hse0 $HmC] as %err' ⟨%Herr', -, -⟩
    · iframe #; ipureintro; exact fun h => (h rfl).elim
    obtain ⟨H1, -⟩ := Herr'
    rw [H1 rfl]
    iapply HΦ
    isplitr
    · iintro %h; exact absurd rfl h.1
    iframe HR
    unfold rangeCallOut
    ileft
    iframe
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    icases Heo with (#Hci | Heo)
    · -- (incomingof Part B) `kv.Do`'s error is the context's: `ContextError` at its message keeps it a
      -- context error, or gives it a context message as its description (no handler's)
      iunfold go_etcd_io.etcd.cache.v3.ctxErrIs at Hci
      icases Hci with ⟨%e0, %m0, %H0, #Hm0⟩
      ihave #HmC : go_etcd_io.etcd.cache.v3.descIs (GF := GF) err m0 $$ []
      · rw [H0.1]
        iapply (ctxErr_descIs e0 m0 (H0.1 ▸ Hce') H0.2.2) $$ Hm0
      wp_apply wp_ContextError ci cd err m0 $$ [$Hse $HmC] as %err' ⟨%Herr', #Hse', #Hclw, -, #Hback⟩
      · iframe #; ipureintro; exact fun _ => Hce'
      ihave #Hcl' := Hclw $$ Hcl
      iapply HΦ
      isplitr
      · iintro %h
        icases Hback with (%hn | #hctx | #hm)
        · exact absurd ⟨e0, H0.1, H0.2.1, H0.2.2⟩ hn
        · iright
          iunfold go_etcd_io.etcd.cache.v3.ctxErrIs at hctx
          icases hctx with ⟨%e', %m', %H', -⟩
          ipureintro; exact ⟨e', H'.1, H'.2.2⟩
        · ileft
          iapply ifcErrOut_notin
          unfold notHandlerErr go_etcd_io.etcd.cache.v3.notDescIn
          isplitr
          · ipureintro; exact h.1
          iexists m0
          iframe hm
          ipureintro; exact ctxErrMsg_not_handler H0.2.1
      iframe HR
      unfold rangeCallOut
      iright
      iframe #
      ipureintro
      exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩
    · -- (errdesc stage 2b) the description `ContextError` keeps is fixed at its call: the attempt's
      -- (`ifcErrOut`'s), for a valid sort option; any other, for an invalid one
      cases hsv : sortValid (opGetModel key gs)
      · ihave ⟨%mC, #HmC⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hse
        wp_apply wp_ContextError ci cd err mC $$ [$Hse $HmC] as %err' ⟨%Herr', #Hse', #Hclw, -, -⟩
        · iframe #; ipureintro; exact fun _ => Hce'
        ihave #Hcl' := Hclw $$ Hcl
        iapply HΦ
        isplitr
        · iintro %h; exact absurd h.2 (by simp [hsv])
        iframe HR
        unfold rangeCallOut
        iright
        iframe #
        ipureintro
        exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩
      ihave Heo1 := Heo $$ %(⟨Ht, Hne, rfl⟩)
      iunfold ifcErrOut at Heo1
      icases Heo1 with ⟨%d, #Hd, Heo1⟩
      wp_apply wp_ContextError ci cd err d $$ [$Hse $Hd] as %err' ⟨%Herr', #Hse', #Hclw, #Hd', -⟩
      · iframe #; ipureintro; exact fun _ => Hce'
      ihave #Hcl' := Hclw $$ Hcl
      iapply HΦ
      isplitl [Heo1]
      · iintro %h
        icases Hd' with (Hd' | #hctx)
        · icases Hd' with (%hd | #Hd2)
          · exact absurd hd Hne
          ileft
          iapply (ifcErrOut_intro _ _ _ _ d) $$ Hd2 Heo1
        · iright
          iunfold go_etcd_io.etcd.cache.v3.ctxErrIs at hctx
          icases hctx with ⟨%e', %m', %H', -⟩
          ipureintro; exact ⟨e', H'.1, H'.2.2⟩
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
  iintro %Φ ⟨Hlt, #Pc, #Hkv, #Hctx, #Hce, #Hopts, HR, #Hsn, %Hnp, #Hk, #Hrun, %Hsz⟩ HΦ
  ihave #HctxO := ctxOk_outgoingC ci cd $$ Hctx
  iunfold metadata.outgoingCtxOkC at HctxO
  icases HctxO with ⟨%om, #Hom⟩
  iunfold isKV at Hkv
  icases Hkv with ⟨#Hobj, #Hregs⟩
  icases (kvObjAt_conn api (ms.map SrvAt.addr)).1 $$ Hobj with ⟨%conn, #Hobj⟩
  iapply (wp_Get api conn (ms.map SrvAt.addr) ci om cd key sl gs R (kvRangeSpecE ms)
    (rangeAns ms c F (rangeWireOf (opGetModel key gs)) Q)
    (rangeErrΨ ms c F (rangeWireOf (opGetModel key gs)) Q)) $$ [HR]
  · iframe #
    iframe HR
    isplitl []
    · ipureintro; exact Hnp
    isplitl []
    · iapply (kvRegs_rpcRangeE ms) $$ Hregs
    isplitl []; rotate_left
    · ipureintro; exact Hsz
    imodintro
    inext
    unfold attemptPre
    iintro %md -
    iapply (rangeSpecE_of ms c F (rangeWireOf (opGetModel key gs)) Q md)
    iframe Hk Hrun
  inext
  iintro %resp %err ⟨Heo, HR, Hout⟩
  iapply HΦ
  iframe HR Hout
  iintro %hs
  unfold rangeErrOut
  iintro %h
  ihave Heo' := Heo $$ %(And.intro h.1 hs)
  icases Heo' with (Heo' | %hctx)
  · ileft
    iapply (rangeErrΨ_of_ifc ms c F _ Q err h.2)
    iexact Heo'
  · iright; ipureintro; exact hctx

theorem kv.Get.wp_proof
    (wp_NewOp : NewOp.spec (GF := GF) (hG := hG))
    (wp_Do : kv.Do.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Get.spec (GF := GF) (hG := hG) := by
  intro api γ dup ci cd key sl gs R Q
  wp_start as ⟨Hlt, #Hkv, #Hctx, #Hce, #Hopts, HR, #Hsn, %Hnp, #Hrun, %Hsz⟩
  obtain ⟨Hnp, Ht⟩ := Hnp
  wp_auto
  wp_apply (opGet_res wp_NewOp key sl gs R) $$ [$HR] as %opv ⟨#Hat, HR⟩
  · iframe #; ipureintro; exact Hnp
  wp_apply wp_Do api γ dup ci cd opv (opGetModel key gs) Q $$ []
    as %r %err Hout
  · iframe #
    isplitl []; rotate_left
    · ipureintro; exact Hsz
    unfold doRunOk
    ileft
    iframe #
    ipureintro; exact Ht
  ihave Hout' : rangeCallOut (rangeStOk (rangeWireOf (opGetModel key gs)) Q) r.get' err
      $$ [Hout]
  · have Heq : doOut (opGetModel key gs) (putStOk γ (putWireOf (opGetModel key gs)) Q)
        (rangeStOk (rangeWireOf (opGetModel key gs)) Q)
        (delStOk (deleteWireOf (opGetModel key gs)) Q) r err =
        rangeCallOut (rangeStOk (rangeWireOf (opGetModel key gs)) Q) r.get' err := by
      unfold doOut; rw [Ht]; simp only [↓reduceIte]
    rw [← Heq]; iexact Hout
  imod rangeCallOut_persist _ _ _ $$ Hout' with Hout'
  iunfold rangeCallOutP at Hout'
  icases Hout' with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · subst Herr
    ihave #Hse0 := go_etcd_io.etcd.cache.v3.statusErrOk_nil (GF := GF)
    ihave ⟨%mC, #HmC⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hse0
    wp_apply wp_ContextError ci cd GoInterface.nil mC $$ [$Hse0 $HmC] as %err' ⟨%Herr', -, -⟩
    · iframe #; ipureintro; exact fun h => (h rfl).elim
    obtain ⟨H1, -⟩ := Herr'
    rw [H1 rfl]
    iapply HΦ
    iframe HR
    iapply rangeCallOut_st
    unfold rangeCallOutP
    ileft
    iframe
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    ihave ⟨%mC, #HmC⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hse
    wp_apply wp_ContextError ci cd err mC $$ [$Hse $HmC] as %err' ⟨%Herr', #Hse', #Hclw, -⟩
    · iframe #; ipureintro; exact fun _ => Hce'
    ihave #Hcl' := Hclw $$ Hcl
    iapply HΦ
    iframe HR
    iapply rangeCallOut_st
    unfold rangeCallOutP
    iright
    iframe #
    ipureintro
    exact ⟨(Herr'.2 Hne).1, (Herr'.2 Hne).2, Hnull⟩

end proof

end EtcdGrove
end Perennial

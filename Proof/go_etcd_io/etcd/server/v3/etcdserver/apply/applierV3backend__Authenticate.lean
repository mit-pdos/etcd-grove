/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Authenticate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__newHeader
public import Spec.context.WithValue
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.WriteLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]


theorem apply.applierV3backend.Authenticate.wp_proof
    (hWV : context.WithValue.spec (GF := GF) (hG := hG))
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.Authenticate.spec (GF := GF) (hG := hG) := by
  intro E p r log Pre Q Post info
  wp_start as ⟨#Hb, ⟨⟨⟨%am, #Hr⟩, HRW⟩, %Hadm⟩, Htt, Hpre, #HSplit⟩
  icases apply.mPreW_split $$ Hpre with ⟨%cr, %B, Hsw, Hcs, Hwt, Hrt, Htie, Hres, Hkv⟩
  ihave #Hb' := Hb
  iunfold apply.backendIs at Hb'
  icases Hb' with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨-, -, -, -, -, #Has, -, -, -, -, #Hci⟩
  iunfold apply.isAuthStore at Has
  icases Has with ⟨%ai, %Hai, -, -, -, -, -, -, -, -, -, #HM, -⟩
  iunfold apply.isConsistentIndexer at Hci
  icases Hci with ⟨%cii, %Hcii, #HCI⟩
  iunfold apply.authenticateIs at Hr
  icases Hr with ⟨%Hrnn, #Hname, #Hpw, #Htok⟩
  iStructNamed Hopts
  wp_auto
  wp_apply context.wp_Background
  rw [Hcii]
  -- the consistent index's resources, lent out of the critical section's precondition (D14i)
  iunfold srvApi.csContractA at Hcs
  icases Hcs with ⟨HPre, Hhk, Hfin⟩
  iunfold apply.ciSplit at HSplit
  icases HSplit $$ HPre with ⟨%C, %ci, %HC, HC, HCb⟩
  ihave #HCIC := HCI $$ %C %ci
  ihave #HCIC := HCIC $$ []
  · ipureintro; exact HC
  wp_bind (App (Val #(methods cii.ty go!"ConsistentIndex" cii.v)) (Val #()))
  iapply HCIC $$ HC
  inext
  iintro HC
  (try wp_auto)
  ihave HPre := HCb $$ HC
  ihave Hcs : srvApi.csContractA (E.Pk B) E.f Pre Q Post $$ [HPre Hhk Hfin]
  · iunfold srvApi.csContractA; iframe HPre Hhk Hfin
  wp_apply (hWV context.backgroundCtxVal
      ⟨go_etcd_io.etcd.server.v3.auth.AuthenticateParamIndex.ty, _⟩ _) as %c1 ⟨%Hc1, -⟩
  · ipureintro; exact Or.inl rfl
  rcases c1 with c1i | _
  case nil => exact absurd rfl Hc1
  wp_apply (hWV c1i
      ⟨go_etcd_io.etcd.server.v3.auth.AuthenticateParamSimpleTokenPrefix.ty, _⟩ _) as %c2 ⟨-, -⟩
  · ipureintro; exact Or.inr (Or.inl rfl)
  rw [Hai]
  wp_apply HM $$ %c2 %am.name %am.password %B %Pre %Q %Post [$Hcs $HRW $Hwt $Hrt $Htie] as %resp %err ⟨HPP, Hrt, Htie, Hhdr, #HeI, HRW⟩
  · ipureintro; exact Hadm
  wp_if_destruct
  · -- no response
    iapply HΦ
    isplitl [Htt]
    · iexact Htt
    isplitl; rotate_left
    · first | iexact HeI | iapply applyErrIs_nil
    iapply (apply.mPostW_backend _ _ _ _ _ B cr)
    iframe
  · -- a response: its header
    iunfold apply.respHdrOk at Hhdr
    icases Hhdr with (%Hn | ⟨%h0, Hh⟩)
    · exact absurd Hn Hif
    wp_apply (hHdr E p log cr) $$ [$Hpkg $Hb $Htt $Hsw] as %h ⟨Htt, Hsw, -⟩
    iapply HΦ
    isplitl [Htt]
    · iexact Htt
    isplitl; rotate_left
    · first | iexact HeI | iapply applyErrIs_nil
    iapply (apply.mPostW_backend _ _ _ _ _ B cr)
    iframe

end proof

end EtcdGrove
end Perennial

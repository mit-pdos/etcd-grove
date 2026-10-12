/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__Authenticate
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.applierV3backend__newHeader
public import Spec.context.WithValue

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]


theorem apply.applierV3backend.Authenticate.wp_proof
    (hWV : context.WithValue.spec (GF := GF) (hG := hG))
    (hHdr : apply.applierV3backend.newHeader.spec (GF := GF) (hG := hG)) :
    apply.applierV3backend.Authenticate.spec (GF := GF) (hG := hG) := by
  intro E p r log Pre Q Post
  wp_start as ⟨#Hb, ⟨%am, #Hr⟩, Hpre⟩
  iunfold apply.mPre at Hpre
  icases Hpre with ⟨Hkv, Hres, Hcs⟩
  ihave #Hb' := Hb
  iunfold apply.backendIs at Hb'
  icases Hb' with ⟨%opts, #Hopts, #Hok⟩
  iunfold apply.backendOptsOk at Hok
  icases Hok with ⟨-, -, -, -, #Has, -, -, -, -, #Hci⟩
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
  wp_apply HCI as %ci -
  wp_apply (hWV context.backgroundCtxVal
      ⟨go_etcd_io.etcd.server.v3.auth.AuthenticateParamIndex.ty, _⟩ _) as %c1 ⟨%Hc1, -⟩
  · ipureintro; exact Or.inl rfl
  rcases c1 with c1i | _
  case nil => exact absurd rfl Hc1
  wp_apply (hWV c1i
      ⟨go_etcd_io.etcd.server.v3.auth.AuthenticateParamSimpleTokenPrefix.ty, _⟩ _) as %c2 ⟨-, -⟩
  · ipureintro; exact Or.inr (Or.inl rfl)
  rw [Hai]
  wp_apply HM $$ %c2 %am.name %am.password %Pre %Q %Post [$Hcs] as %resp %err ⟨HPP, Hhdr, #HeI⟩
  iunfold apply.kvOwn at Hkv
  icases Hkv with ⟨Hrd, Hsw, Hknown⟩
  wp_if_destruct
  · -- no response
    iapply HΦ
    isplitl; rotate_left
    · first | iexact HeI | iapply applyErrIs_nil
    iunfold apply.mPost
    iunfold apply.kvOwn
    iframe
  · -- a response: its header
    iunfold apply.respHdrOk at Hhdr
    icases Hhdr with (%Hn | ⟨%h0, Hh⟩)
    · exact absurd Hn Hif
    wp_apply (hHdr E p log) $$ [$Hpkg $Hb $Hrd $Hsw] as %h ⟨Hrd, Hsw, -⟩
    iapply HΦ
    isplitl; rotate_left
    · first | iexact HeI | iapply applyErrIs_nil
    iunfold apply.mPost
    iunfold apply.kvOwn
    iframe

end proof

end EtcdGrove
end Perennial

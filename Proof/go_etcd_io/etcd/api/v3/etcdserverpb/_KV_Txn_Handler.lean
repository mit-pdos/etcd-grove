/-
Proof of `Spec/go_etcd_io/etcd/api/v3/etcdserverpb/_KV_Txn_Handler.lean` (unit P3b). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._KV_Txn_Handler

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.etcdserverpb.Assumptions]

theorem etcdserverpb._KV_Txn_Handler.wp_proof :
    etcdserverpb._KV_Txn_Handler.spec (GF := GF) (hG := hG) := by
  intro Req Rep Spec srv S ics Rs Q m Φ' ci cd dec ui hReq hRep hsrv
  wp_start as ⟨#Hblank, #Hh, #Hics, #HQ, HS, HRs, #Hctx, #Hrc, #Hdec, #Hchain, HSpec⟩
  wp_auto
  ihave Hb := Hblank $$ %«$r0_ptr» «$r0»
  ihave #Hdec' := grpcDecOk_ty dec Req m _ hReq $$ Hdec
  ihave #Hd2 := Hdec' $$ %«$r0_ptr»
  wp_bind (App (Val #dec) _)
  iapply Hd2 $$ Hb
  inext
  iintro %err Herr
  icases Herr with (⟨%Herr, #Hr⟩ | %Herr)
  · subst Herr
    wp_auto
    wp_if_destruct
    · simp only [hsrv]
      wp_auto
      iunfold grpcHandlerOk at Hh
      wp_bind (App (App (Val _) (Val #(GoInterface.ok ci))) (Val #«$r0_ptr»))
      iapply Hh $$ %m %Φ' %ci %cd %«$r0_ptr» [HS HSpec]
      · iframe; iframe #
      inext
      iintro %resp %err' ⟨HS, Hres⟩
      wp_auto
      iapply HΦ
      iframe
      iintro %Hnil
      ihave ⟨%m', Hm', HΦ'⟩ := Hres $$ %Hnil
      iexists resp, m'
      iframe
      ipureintro; rw [hRep]
    · cases ics with
      | nil =>
        iunfold grpcSrvChain at Hchain
        icases Hchain with %Hc
        exact absurd Hc Hif
      | cons ic ics' =>
        iunfold grpcSrvChain at Hchain
        icases Hchain with ⟨-, #Hchain⟩
        iStructNamed «$r0»
        ipersist FullMethod
        ipersist srv
        ihave #HQr := HQ $$ Hr
        ihave #Hinfo : srvInfoIs (GF := GF) «$r0_ptr» $$ []
        · iunfold srvInfoIs
          iexists _
          iexact FullMethod
        wp_bind (App (App (App (App (Val #ui) _) _) _) _)
        iapply Hchain
        iapply srvChainWP_of_ok
        iframe #
        iframe
        isplit
        · iintro %ci' %cd' #Hctx' #Hrc'
          iunfold srvHandlerCall
          wp_auto
          simp only [hsrv]
          wp_auto
          iunfold grpcHandlerOk at Hh
          wp_bind (App (App (Val _) (Val #(GoInterface.ok ci'))) (Val _))
          iapply Hh $$ %m %Φ' %ci' %cd' %_ [HS HSpec]
          · iframe; iframe #
          inext
          iintro %resp %err' ⟨HS, Hres⟩
          wp_auto
          iexists _, _
          isplitr
          · ipureintro; rfl
          iintro HRs
          wp_auto
          iapply HΦ
          iframe
          iintro %Hnil
          ihave ⟨%m', Hm', HΦ'⟩ := Hres $$ %Hnil
          iexists resp, m'
          iframe
          ipureintro; rw [hRep]
        · iintro HRs %err' %Herr'
          wp_auto
          iapply HΦ
          iframe
          iintro %Hc
          exact absurd Hc Herr'
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei =>
      wp_auto
      iapply HΦ
      iframe
      iintro %Hc
      cases Hc

end proof

end EtcdGrove
end Perennial

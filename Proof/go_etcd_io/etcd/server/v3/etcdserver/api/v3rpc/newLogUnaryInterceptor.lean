/-
Proof of the spec of the same name (unit P3b, updated for PR etcd#21401). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.newLogUnaryInterceptor
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RequestID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.requestid.NewContext
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_uber_org.zap.Logger__Core
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.logUnaryRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.requestLogFields
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.logUnaryResponseStats

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3 go_uber_org

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.newLogUnaryInterceptor.wp_proof
    (wp_RequestID : EtcdServer.RequestID.spec (GF := GF) (hG := hG))
    (wp_NewContext : requestid.NewContext.spec (GF := GF) (hG := hG))
    (wp_Logger : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (wp_Core : zap.Logger.Core.spec (GF := GF) (hG := hG))
    (wp_logReq : v3rpc.logUnaryRequest.spec (GF := GF) (hG := hG))
    (wp_fields : v3rpc.requestLogFields.spec (GF := GF) (hG := hG))
    (wp_logResp : v3rpc.logUnaryResponseStats.spec (GF := GF) (hG := hG)) :
    v3rpc.newLogUnaryInterceptor.spec (GF := GF) (hG := hG) := by
  intro s lg wd
  wp_start as ⟨#Hlg, %Hlgn, #Hwd⟩
  wp_pures
  wp_alloc_auto
  irename : (s_ptr ↦ s : IProp GF) => Hs
  ipersist Hs
  wp_auto
  rw [recv_eq_func_mk]
  iapply HΦ
  iintro !> %γi %C #Hgen #Hcred #HC
  unfold srvInterceptorOk
  iintro !> %ci %cd %req %info %h %Ψ HR #Hctx #Hrc _ #Hinfo #HQ Hk
  wp_auto
  wp_apply wp_RequestID s γi $$ [] as %reqID Hfr
  · iframe #
  wp_apply wp_NewContext ci reqID $$ [] as %c ⟨_, %ci', %vs, %Hc', -, #HisCtx', -, #Hreqid, #Hval⟩
  subst Hc'
  ihave #Hctx' := HisCtx' $$ %cd Hctx
  ihave #Hrc' : grpcRunCtx (GF := GF) ci' $$ []
  · iunfold grpcRunCtx
    iunfold grpcRunCtx at Hrc
    iintro !> %n %x %Φ' ⟨%Hpref, %Hne⟩ HΦ'
    iapply Hval $$ %n %x %Φ'
    · ipureintro; exact Hne
    iapply Hrc $$ %n %x %Φ' %(⟨Hpref, Hne⟩) HΦ'
  ihave HreqCtx : reqIdCtxAt (GF := GF) γi ci' $$ [Hfr]
  · iapply (reqIdCtxAt_of_some γi ci' reqID)
    iframe Hfr
    iframe #
  ihave HC' := HC $$ %ci' HreqCtx
  wp_apply wp_Logger s lg $$ [HR] as ⟨-, HR⟩
  · iframe; iframe #; ipureintro; exact Hlgn
  wp_apply wp_Core lg $$ [] as %c ⟨%core, %Hc, #Hcore⟩
  · iframe #; ipureintro; exact Hlgn
  subst Hc
  wp_auto
  iunfold zap.coreSpec at Hcore
  wp_apply Hcore as %debug -
  cases debug
  · wp_auto
    wp_apply time.wp_Now as %startTime -
    icases Hk with ⟨Hk, -⟩
    ihave Hk := Hk $$ %ci' %{ cd with Values := vs } Hctx' Hrc' HC'
    wp_bind (App (App (Val #h) _) _)
    iapply (wp_wand (Φ := fun v => iprop(∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗
      (srvLgReader s -∗ Ψ v)))) $$ Hk
    iintro %v ⟨%resp, %err, %Hv, HΨ⟩
    subst Hv
    wp_auto
    wp_apply time.wp_Since as %duration -
    wp_if_destruct
    · wp_apply wp_fields req $$ [] as %fields -
      · iframe #
      wp_apply wp_logResp (GoInterface.ok ci') lg go!"Warn" duration info startTime resp fields $$ []
      · iframe #; ipureintro; exact ⟨Hlgn, Or.inr rfl⟩
      iapply HΨ
      iexact HR
    · iapply HΨ
      iexact HR
  · wp_auto
    wp_apply wp_logReq (GoInterface.ok ci') lg go!"Debug" info req $$ []
    · iframe #; ipureintro; exact ⟨Hlgn, Or.inl rfl⟩
    wp_apply time.wp_Now as %startTime -
    icases Hk with ⟨Hk, -⟩
    ihave Hk := Hk $$ %ci' %{ cd with Values := vs } Hctx' Hrc' HC'
    wp_bind (App (App (Val #h) _) _)
    iapply (wp_wand (Φ := fun v => iprop(∃ resp err : GoInterface, ⌜v = PairV #resp #err⌝ ∗
      (srvLgReader s -∗ Ψ v)))) $$ Hk
    iintro %v ⟨%resp, %err, %Hv, HΨ⟩
    subst Hv
    wp_auto
    wp_apply time.wp_Since as %duration -
    wp_if_destruct
    · wp_apply wp_logResp (GoInterface.ok ci') lg go!"Warn" duration info startTime resp slice.nil $$ []
      · iframe #; ipureintro; exact ⟨Hlgn, Or.inr rfl⟩
      iapply HΨ
      iexact HR
    · wp_apply wp_logResp (GoInterface.ok ci') lg go!"Debug" duration info startTime resp slice.nil $$ []
      · iframe #; ipureintro; exact ⟨Hlgn, Or.inl rfl⟩
      iapply HΨ
      iexact HR

end proof

end EtcdGrove
end Perennial

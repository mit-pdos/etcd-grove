/- Lean-first (no Rocq counterpart).

# `Server`'s proof

The service (`service.New`) registered on `DefaultServer`'s owned registry (`Register.spec_fresh`:
`"Svc"` is free, so the registration succeeds), `&NoMethods{}` refused (`Register.spec_none`), the rpc
handler on `DefaultServeMux` (`HandleHTTP.spec`), then net/http's server at `HTTPAddr` in a goroutine
of its own (`Serve.spec_rpc`) and raw net/rpc at `TCPAddr` (`Accept.spec`). Every address the server
listens at serves the registered service (`srvServes`, from `drvSS_only`).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Server
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.service.New
public import Net.Spec.net.rpc.Register
public import Net.Spec.net.rpc.HandleHTTP
public import Net.Spec.net.rpc.Accept
public import Net.Spec.net.http.Serve
public import Net.Spec.net.Listen
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Codec

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- Every address of the run serves the registered `"Svc"`. -/
theorem drv_srvServes (γid reg γs : GName) (a : GoString) :
    net.rpc.svcReg (GF := GF) γs drvCodec go!"Svc" (echoSvc γid) ⊢
      net.rpc.srvServes γs drvCodec (drvWorld γid reg) a := by
  iintro #Hreg
  unfold net.rpc.srvServes
  imodintro
  iintro %svc %S %hS
  obtain ⟨rfl, rfl⟩ := drvSS_only γid a svc S hS
  iframe Hreg
  iapply echoSvc_errOk

theorem Server.wp_proof (svcRcv : svcRcv.spec (GF := GF) (hG := hG))
    (noMethodsRcv : noMethodsRcv.spec (GF := GF))
    (wp_New : service.New.spec (GF := GF) (hG := hG))
    (wp_RegisterFresh : net.rpc.Register.spec_fresh (GF := GF) (hG := hG))
    (wp_RegisterNone : net.rpc.Register.spec_none (GF := GF) (hG := hG))
    (wp_HandleHTTP : net.rpc.HandleHTTP.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Serve : net.http.Serve.spec_rpc (GF := GF) (hG := hG))
    (wp_Accept : net.rpc.Accept.spec (GF := GF) (hG := hG)) :
    Server.spec (GF := GF) (hG := hG) := by
  intro γid reg γs γf
  wp_start as ⟨#Hf, #Hset, %Hb, #Hhttp, #Hlog, #Hsvcp, #Henv, #Hcon, #Hsenv, #Hds, Hown, Hmux,
    #Htl, #Hhl⟩
  wp_auto
  wp_apply wp_New γid $$ Hsvcp as %s ⟨%Hsnn, #Hsvc⟩
  wp_auto
  wp_apply wp_RegisterFresh γs γf ∅ drvCodec _ (echoSvc γid) go!"Svc" (W8 83) go!"vc" rfl
      (by decide) $$ [Hown] as %err1 ⟨%He1, #Hreg, Hown⟩
  · iframe Hds Hown Hset
    isplitr
    · ipureintro; simp
    iapply svcRcv
    iframe Hset Hsvc
    ipureintro; exact Hsnn
  subst He1
  wp_auto
  ihave #Hsrv := drv_srvServes γid reg γs tcpAddr $$ Hreg
  ihave #Hsrvh := drv_srvServes γid reg γs httpAddr $$ Hreg
  ihave #Hdsa := net.rpc.defaultServerO_any γs γf $$ Hds
  -- `&NoMethods{}` refused
  wp_apply wp_RegisterNone γs drvCodec _ go!"NoMethods" (W8 78) go!"oMethods" rfl (by decide)
      $$ [] as %err2 %He2
  · iframe Hdsa Hset Hlog
    iapply noMethodsRcv
    ipureintro; exact ?_
  cases err2 with
  | nil => exact absurd rfl He2
  | ok e2 =>
  wp_auto
  iunfold drvFacts at Hf
  icases Hf with ⟨-, %fr, #Hrg, #Hrf⟩
  wp_bind (App (Val #fr) (Val _))
  iapply wp_wand $$ (Hrf $$ %go!"register")
  iintro %v %Hv
  subst Hv
  wp_auto
  -- the rpc handler on `DefaultServeMux`
  wp_apply wp_HandleHTTP γs drvCodec (drvWorld γid reg) (fun a => a = httpAddr) [] (by simp)
      (by simp) $$ [Hmux] as ⟨Hmux, #Hrpc⟩
  · iframe Hhttp Hmux Hdsa Henv Hset Hcon
    isplitr
    · ipureintro; exact Hb
    imodintro
    iintro %a %ha
    subst ha
    iframe Hsrvh
    ipureintro
    exact ⟨by simp [(drvWorld_http (GF := GF) γid reg).2.1, net.rpc.connectReq],
      (drvWorld_http (GF := GF) γid reg).2.2⟩
  -- listen at `HTTPAddr`, serve HTTP in a goroutine
  ihave %Hhok := net.rpc.rpcLisP_ok _ _ _ _ $$ Hhl
  wp_apply wp_Listen go!"tcp" net.tcpNet_tcp httpAddr as %hv %herr Hl
  · isplitr
    · ipureintro; exact Hhok
    iapply net.rpc.rpcLisP_lis
    iexact Hhl
  icases Hl with (⟨%He, %hl, #Hhli, Hhnl, #Hhon⟩ | ⟨%x, -, #Hre⟩)
  rotate_left
  · ihave %Hne := net.resErr_netErr $$ Hre
    have hne := net.netErr_ne_nil (Hne.2 (by simp))
    rcases herr with ei | _
    · wp_auto
      iapply HΦ; itrivial
    · exact absurd rfl hne
  subst He
  wp_auto
  iapply fupd_wp
  imod (lisInv_alloc ⊤ _ hl httpAddr true) $$ Hhnl with #Hhinv
  imodintro
  wp_bind (Fork _)
  iapply wp_fork_tok
  inext
  iintro Htok
  isplitl [Htok]
  · wp_apply (wp_Serve (drvWorld γid reg) httpAddr net.rpc.defaultRPCPath hv hl
      net.rpc.HandleHTTP.litPattern_rpc) $$ [Htok] as %e3 Htok
    · iframe Hhttp Hsenv Hhli Hhon Hhinv Htok
      isplitr
      · ipureintro; exact Hb
      isplitr
      · rw [show (net.rpc.connectReq net.rpc.defaultRPCPath) = net.rpc.connectReq net.rpc.defaultRPCPath from rfl]
        iexact Hhl
      iunfold net.http.muxRpc at Hrpc
      iunfold net.http.muxRpc
      icases Hrpc with ⟨%h, #Hroute, #Hh⟩
      iexists h
      iframe Hroute
      imodintro
      iintro %a %ha
      iapply Hh
      ipureintro
      exact ((lisAccepts_addrOk (by decide)).1 ha.2).symm
    iframe Htok
    ipureintro; exact isPanic_intoVal _
  -- listen at `TCPAddr`, serve raw net/rpc
  ihave %Htok' := net.rpc.rpcLisP_ok _ _ _ _ $$ Htl
  wp_apply wp_Listen go!"tcp" net.tcpNet_tcp tcpAddr as %tv %terr Hl
  · isplitr
    · ipureintro; exact Htok'
    iapply net.rpc.rpcLisP_lis
    iexact Htl
  icases Hl with (⟨%He, %tl, #Htli, Htnl, #Hton⟩ | ⟨%x, -, #Hre⟩)
  rotate_left
  · ihave %Hne := net.resErr_netErr $$ Hre
    have hne := net.netErr_ne_nil (Hne.2 (by simp))
    rcases terr with ei | _
    · wp_auto
      iapply HΦ; itrivial
    · exact absurd rfl hne
  subst He
  wp_auto
  iapply fupd_wp
  imod (lisInv_alloc ⊤ _ tl tcpAddr true) $$ Htnl with #Htinv
  imodintro
  wp_apply wp_Accept γs drvCodec (drvWorld γid reg) tcpAddr tv tl $$ [] as -
  · iframe Hdsa Henv Hset Hlog Htli Hton Htinv
    isplitr
    · ipureintro; exact Hb
    imodintro
    iintro %a ⟨%hok, %hacc⟩
    have ha : a = tcpAddr := ((lisAccepts_addrOk (by decide)).1 hacc).symm
    subst ha
    iframe Hsrv
    iapply net.rpc.rpcLisP_addr _ _ _ _ _ hok hacc
    iexact Htl
  wp_auto
  iapply HΦ
  itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial

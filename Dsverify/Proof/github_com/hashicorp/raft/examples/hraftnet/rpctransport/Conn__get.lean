/-
The proof of `rpctransport.Conn.get`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn__get
public import Net.Proof.net.rpc.ProtoGhost
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Net.Spec.net.DialTimeout
public import Net.Spec.net.rpc.NewClient

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.rpctransport

theorem github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn.get.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_DialTimeout : net.DialTimeout.spec (GF := GF) (hG := hG))
    (wp_NewClient : net.rpc.NewClient.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn.get.spec (GF := GF) (hG := hG) := by
  intro p W a d
  wp_start as #Hc
  ihave #Henv := dialEnv_of_pkg $$ Hpkg
  iunfold dialEnv at Henv
  icases Henv with ⟨#Hnet, #Hsync, #Htime, #Hce, ⟨%et, #Het⟩, ⟨%ed, #Hed⟩⟩
  iunfold isConn at Hc
  icases Hc with ⟨#Haddr, #Hmu, #Hra, %Hrb⟩
  wp_auto
  wp_apply wp_Lock $$ [$Hmu] as ⟨Hlk, Hinv⟩
  iunfold connInv at Hinv
  icases Hinv with ⟨%c0, Hc0, Hcc⟩
  wp_auto
  wp_if_destruct
  · ihave #Hra' := Hra
    iunfold net.rpc.rpcAddr at Hra'
    iunfold net.rpc.rpcAddrP at Hra'
    icases Hra' with ⟨#Hap, #Hreg, ⟨%Hhs, %HhsA⟩⟩
    ihave %Hok := addrTok_ok $$ [Hap]
    · iapply addrProto_tok $$ Hap
    wp_apply wp_DialTimeout go!"tcp" net.tcpNet_tcp a d et ed iprop(True)
        (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false (net.rpc.reqProto W a)
          (net.rpc.respProto W a) [] [] ∗ connFresh (Gg := hG.goose_globalGS) cn false)) $$ [Hap]
      as %nc %err (⟨%Herr, %cn, #Hnc, Hend, Hfresh⟩ | ⟨-, %x, %e, -, #Hoe, -⟩)
    · (try iframe Hnet)
      (try iframe Het)
      (try iframe Hed)
      isplitr
      · ipureintro; exact Hok
      isplit
      · itrivial
      · iapply dial_au $$ Hap
    · subst Herr
      iunfold net.isConn at Hnc
      icases Hnc with ⟨%t, %la, %ra, %Hct, #Hca⟩
      subst Hct
      iunfold connEnd at Hend
      icases Hend with ⟨Hsend, Hrecv⟩
      ihave Hr : (|={⊤}=> ∃ γ : net.rpc.RpcConnNames, net.rpc.isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗
          monoListAuthOwn γ.reqs (1 : Qp).half ([] : List net.rpc.RpcReq) ∗
          ghostMapAuth γ.nm 1 (∅ : GMap Nat (GName × GName × GName)) : IProp GF) $$ [Hfresh]
      · iapply net.rpc.rpc_register (Gg := hG.goose_globalGS) W a cn $$ [$Hreg $Hfresh]
      imod Hr with ⟨%γ, #Hrpc, Hreqs, Hnm⟩
      wp_auto
      wp_apply wp_NewClient W a cn γ t la ra $$ [$Hce $Hca Hrpc Hreqs Hnm Hsend Hrecv] as %cl #Hcl
      · isplitr
        · ipureintro; exact Hrb
        iunfold net.rpc.rpcDialed
        rw [Hhs, HhsA]
        iframe Hrpc Hreqs Hnm Hsend Hrecv
      (try wp_auto)
      wp_apply wp_Unlock $$ [$Hmu $Hlk Hc0]
      · inext; unfold connInv; iexists _; iframe Hc0; iright; iexact Hcl
      iapply HΦ
      iright; iexact Hcl
    · iunfold net.opErr at Hoe
      icases Hoe with ⟨%pe, %nw, ⟨%Herr, -⟩, -⟩
      subst Herr
      wp_auto
      wp_apply wp_Unlock $$ [$Hmu $Hlk Hc0 Hcc]
      · inext; unfold connInv; iexists _; iframe Hc0; ileft; ipureintro; rfl
      iapply HΦ
      ileft; ipureintro; rfl
  · (try wp_auto)
    ihave #Hcc' : (net.rpc.isClient c0 W a : IProp GF) $$ [Hcc]
    · icases Hcc with (%Hn | #H)
      · exfalso; exact Hif Hn
      · iexact H
    wp_apply wp_Unlock $$ [$Hmu $Hlk Hc0]
    · inext; unfold connInv; iexists _; iframe Hc0; iright; iexact Hcc'
    iapply HΦ
    iright; iexact Hcc'

end proof

end Perennial

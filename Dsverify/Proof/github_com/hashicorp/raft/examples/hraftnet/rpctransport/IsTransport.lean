/-
**The hraft kit transport meets raft's transport contract** (`iface/Net.lean`'s `isTransport`;
notes/dsv-hraft.md, S4): server `i`'s transport `t` (`isTrans`, what `New` returns), as an interface
value, satisfies `isTransport` with its consumer channel, from the specs of its methods (taken as
hypotheses, as a proof takes its callees': the kit's `Link` passes their results). The codec laws
(`CodecLaws`) are `isTrans`'s premise, so the theorem is parametric in them.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__Consumer
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__LocalAddr
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__EncodePeer
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__DecodePeer
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__SetHeartbeatHandler
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__AppendEntriesPipeline
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__AppendEntries
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__RequestVote
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__RequestPreVote
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__InstallSnapshot
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Transport__TimeoutNow

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet.rpctransport

open github_com.hashicorp.raft github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rpctransport.Assumptions]
variable [π : Net.NetProtoGS] [net.rpc.Assumptions] [net.Assumptions]

/-- The transport's consumer channel is server `i`'s RPC channel. -/
theorem isTrans_consumer (t : Loc) (γ : GNames) (snapP : Nat → List w8 → IProp GF) (i : SID)
    (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) :
    isTrans (GF := GF) t γ snapP i W C ⊢
      ∃ ch, t.[Transport, go!"consumer"] ↦□ ch ∗ isRpcChan γ snapP i ch := by
  iintro #Ht
  unfold isTrans
  iNamed Ht
  iexists ch
  iframe Hconsumer Hrpc

/-- **Server `i`'s transport meets the transport contract**, with its consumer channel. -/
theorem Transport_isTransport
    (wp_Consumer : Transport.Consumer.spec (GF := GF) (hG := hG))
    (wp_LocalAddr : Transport.LocalAddr.spec (GF := GF) (hG := hG))
    (wp_EncodePeer : Transport.EncodePeer.spec (GF := GF) (hG := hG))
    (wp_DecodePeer : Transport.DecodePeer.spec (GF := GF) (hG := hG))
    (wp_SetHeartbeatHandler : Transport.SetHeartbeatHandler.spec (GF := GF) (hG := hG))
    (wp_AppendEntriesPipeline : Transport.AppendEntriesPipeline.spec (GF := GF) (hG := hG))
    (wp_AppendEntries : Transport.AppendEntries.spec (GF := GF) (hG := hG))
    (wp_RequestVote : Transport.RequestVote.spec (GF := GF) (hG := hG))
    (wp_RequestPreVote : Transport.RequestPreVote.spec (GF := GF) (hG := hG))
    (wp_InstallSnapshot : Transport.InstallSnapshot.spec (GF := GF) (hG := hG))
    (wp_TimeoutNow : Transport.TimeoutNow.spec (GF := GF) (hG := hG))
    (t : Loc) (γ : GNames) (snapP : Nat → List w8 → IProp GF) (i : SID)
    (W : net.rpc.RpcWorld GF) (C : net.rpc.CodecSpec GF) :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rpctransport ∗
      isTrans t γ snapP i W C ⊢
      ∃ ch, isTransport ⟨go.GoType.PointerType Transport.ty, #t⟩ γ snapP i ch := by
  iintro ⟨#Hpkg, #Ht⟩
  icases isTrans_consumer t γ snapP i W C $$ Ht with ⟨%ch, #Hcons, #Hrpc⟩
  iexists ch
  unfold isTransport
  iframe Hrpc
  isplitr
  · imodintro
    iintro %Φ HΦ
    iapply wp_Consumer t γ snapP i W C ch $$ [$Hpkg $Ht $Hcons]
    inext; iintro -; iexact HΦ
  isplitr
  · imodintro
    iintro %Φ HΦ
    iapply wp_LocalAddr t γ snapP i W C $$ [$Hpkg $Ht]
    inext; iintro -; iexact HΦ
  isplitr
  · imodintro
    iintro %id %a %Φ HΦ
    iapply wp_EncodePeer t id a $$ [$Hpkg]
    inext; iexact HΦ
  isplitr
  · imodintro
    iintro %buf %dq %b %Φ Hb HΦ
    iapply wp_DecodePeer t buf dq b $$ [$Hpkg $Hb]
    inext; iexact HΦ
  isplitr
  · imodintro
    iintro %cb %Φ #Hh HΦ
    iapply wp_SetHeartbeatHandler t γ snapP i W C cb $$ [$Hpkg $Ht $Hh]
    inext; iintro -; iexact HΦ
  isplitr
  · imodintro
    iintro %id %j %T %Φ -  HΦ
    iapply wp_AppendEntriesPipeline t γ snapP i W C id j T $$ [$Hpkg $Ht]
    inext; iintro %p %err Hr; iapply HΦ; ileft; iexact Hr
  isplitr
  · imodintro
    iintro %id %j %args %resp %rq %rp0 %dq %snd %T %prev %pt %ents %lci %ss %tid %Φ - Hargs Hrq Hresp Htok HΦ
    iapply wp_AppendEntries t γ snapP i W C id j args resp rq rp0 dq snd T prev pt ents lci ss
      $$ [$Hpkg $Ht $Hargs $Hrq $Hresp]
    inext; iintro %err ⟨Hargs, Hr⟩
    iapply HΦ $$ Hargs Htok
    icases Hr with (Hok | ⟨#He, Hrp⟩)
    · ileft; iexact Hok
    · iright; iframe Hrp; iapply errStr_errOk $$ He
  isplitr
  · imodintro
    iintro %id %j %args %resp %rq %rp0 %dq %c %T %li %lt %tid %Φ - Hargs Hrq Hresp Htok HΦ
    iapply wp_RequestVote t γ snapP i W C id j args resp rq rp0 dq c T li lt
      $$ [$Hpkg $Ht $Hargs $Hrq $Hresp]
    inext; iintro %err ⟨Hargs, Hr⟩
    iapply HΦ $$ Hargs Htok
    icases Hr with (Hok | ⟨#He, Hrp⟩)
    · ileft; iexact Hok
    · iright; iframe Hrp; iapply errStr_errOk $$ He
  isplitr
  · imodintro
    iintro %id %j %args %resp %rq %rp0 %dq %c %T %tid %Φ - Hargs Hrq Hresp Htok HΦ
    iapply wp_RequestPreVote t γ snapP i W C id j args resp rq rp0 dq c T
      $$ [$Hpkg $Ht $Hargs $Hrq $Hresp]
    inext; iintro %err ⟨Hargs, Hr⟩
    iapply HΦ $$ Hargs Htok
    icases Hr with (Hok | ⟨#He, Hrp⟩)
    · ileft; iexact Hok
    · iright; iframe Hrp; iapply errStr_errOk $$ He
  isplitr
  · imodintro
    iintro %id %j %args %resp %rq %rp0 %dq %snd %T %s %st %b %data %tid %Φ - Hargs Hrq Hresp Hs Htok HΦ
    iapply wp_InstallSnapshot t γ snapP i W C id j args resp rq rp0 dq snd T s st b data
      $$ [$Hpkg $Ht $Hargs $Hrq $Hresp $Hs]
    inext; iintro %err ⟨Hargs, Hr⟩
    iapply HΦ $$ Hargs Htok
    icases Hr with (Hok | ⟨#He, Hrp⟩)
    · ileft; iexact Hok
    · iright; iframe Hrp
      ihave #Hok := errStr_errOk err $$ He
      iapply errOk_ne_nil $$ Hok
  · imodintro
    iintro %id %j %args %resp %rq %rp0 %dq %c %tid %Φ - Hargs Hrq Hresp Htok HΦ
    iapply wp_TimeoutNow t γ snapP i W C id j args resp rq rp0 dq c
      $$ [$Hpkg $Ht $Hargs $Hrq $Hresp]
    inext; iintro %err ⟨Hargs, Hr⟩
    iapply HΦ $$ Hargs Htok
    icases Hr with (⟨%He, %rp, Hrp, -⟩ | ⟨#He, Hrp⟩)
    · ileft; iframe %He; iexists rp; iexact Hrp
    · iright
      ihave %Hnf := errStr_errNoFmt err $$ He
      iframe %Hnf
      isplitr
      · iapply errStr_errOk $$ He
      · iexists rp0; iexact Hrp

end results

end github_com.hashicorp.raft.examples.hraftnet.rpctransport

end Perennial

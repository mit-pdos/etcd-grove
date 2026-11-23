/-
Package `replica`: the recorder's gRPC handlers meet their method specs (`handlerOk`, the
generated `_Consensus_*_Handler` over `GRPCConnection`'s methods).
-/
module

public import Dsverify.Proof.raxos.Replica.HandleESP

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src
open hyp.grpc (handlerOk replyOk decOk)
open models_lab.pbcodec (PbCodec)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]

attribute [local instance] hyp.qpCodec


set_option goose.wp.extras true

/-- The service implementation: the recorder's `GRPCConnection`. -/
abbrev connIface (gc : Loc) : GoInterface := interface.mkOk (go.GoType.PointerType GRPCConnection.ty) #gc

theorem wp_GRPCConnection_ESP (γ : QNames) (k : Nat) (gc re lin : Loc) (m : PM)
    (ctx : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
        gc.[GRPCConnection, go!"Recorder"] ↦□ re ∗ isRecorder γ k re ∗
        repPM lin .discard m ∗ ⌜pmOk m⌝ ∗ pmFacts γ m }}
      (App (App (Val (gc @!! go.GoType.PointerType GRPCConnection.ty @!! go!"ESP")) (Val #ctx))
        (Val #lin))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ⌜err = interface.nil⌝ ∗
        ∃ rr, repRR resp .discard rr ∗ espReply γ k m rr }} := by
  wp_start as ⟨#Hgc, #Hre, #Hreq, %Hok, #Hfacts⟩
  wp_auto
  wp_apply wp_HandleESP γ k re lin m $$ [$Hre $Hreq $Hfacts] as %resp ⟨%rr, #Hrr, Hrep⟩
  · ipureintro; exact Hok
  ihave %Hnn : ⌜resp ≠ null⌝ $$ []
  · iunfold repRR at Hrr; icases Hrr with ⟨%x, Hx, -⟩; iapply typedPointsto_not_null $$ Hx
  wp_if_destruct
  · exact absurd rfl Hnn
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iexists rr; iframe #; iframe

theorem esp_handlerOk (γ : QNames) (k : Nat) (gc re : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
      gc.[GRPCConnection, go!"Recorder"] ↦□ re ∗ isRecorder γ k re ⊢
    handlerOk qv.grpc (connIface gc) (functions _Consensus_ESP_Handler []) (espSpec γ k) := by
  iintro ⟨#Hpkg, #Hgc, #Hre⟩
  unfold handlerOk
  imodintro
  iintro %ctx %cd %dec %Got %Θ #Hctx Hdec HΘ
  wp_func_call
  wp_call
  wp_auto
  irename «$r0» => Hin
  generalize «$r0_ptr» = lin at *
  iunfold decOk at Hdec
  wp_apply Hdec $$ %(interface.mkOk (go.GoType.PointerType ProposerMessage.ty) #lin)
      %(fun bs b => if b then iprop(∃ v,
        (⌜∃ v0, pmOk v0 ∧ encPM v0 = bs⌝ -∗ repPM lin (DFrac.own 1) v) ∗
        ⌜∀ v0, pmOk v0 → encPM v0 = bs → v = v0⌝) else iprop(True)) [Hin] as %err Herr
  · iintro %bs
    rw [show (PbCodec.unmarshal (GF := GF)) = unmarshalPre from rfl]
    unfold unmarshalPre
    ileft
    iexists lin
    isplitr
    · ipureintro; rfl
    iframe Hin
    unfold decInto
    isplit
    · iintro %v Hv %Hv0
      simp only [↓reduceIte]
      iexists v; iframe; ipureintro; exact Hv0
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  icases Herr with (⟨%He, Hv⟩ | ⟨%He, #Herr, -⟩)
  rotate_left
  · rcases err with ei | _
    · wp_auto
      iapply HΘ; iright; iframe #; ipureintro; exact He
    · exact absurd rfl He
  subst He
  wp_auto
  icases Hv with ⟨%bs, %Φ, HS, HGot, %v, Hv, %Hv0⟩
  iunfold espSpec at HS
  icases HS with ⟨%m, ⟨%Hbs, %Hmok⟩, #Hfacts, HΦ⟩
  ihave Hv := Hv $$ %(⟨m, Hmok, Hbs.symm⟩ : ∃ v0, pmOk v0 ∧ encPM v0 = bs)
  have Hvm := Hv0 m Hmok Hbs.symm
  subst Hvm
  imod repPM_persist _ _ _ $$ Hv with #Hv
  have Hts : go.typeSetContains (go.GoType.PointerType GRPCConnection.ty) ConsensusServer.ty =
    true := by go_type_set
  simp only [Hts, ↓reduceIte]
  wp_auto
  wp_apply wp_GRPCConnection_ESP γ k gc re lin v _ $$ [$Hgc $Hre $Hv $Hfacts]
    as %resp %err ⟨%Herr, %rr, #Hrr, Hrep⟩
  · ipureintro; exact Hmok
  subst Herr
  iapply HΘ
  ileft
  isplitr
  · ipureintro; rfl
  iexists Φ
  iframe HGot
  unfold replyOk
  iright
  isplitr
  · ipureintro; nofun
  rw [show (PbCodec.marshal (GF := GF)) = marshalPre from rfl]
  unfold marshalPre
  iright; ileft
  iexists resp, DFrac.discard, rr
  isplitr
  · ipureintro; rfl
  iframe #
  iintro -
  unfold espReply
  icases Hrep with ⟨%Hrok, Hcase⟩
  isplit
  · iintro - %bs' %Hbs'
    cases Hbs'
    iapply HΦ
    iframe; ipureintro; exact Hrok
  · iintro %Hn; exact absurd Hrok Hn
  done

end proof

end Perennial.raxos

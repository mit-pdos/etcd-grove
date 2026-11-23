/-
Package `proposer`: `runProposer` (the proposer's goroutine: a `select` over its three input
channels, forever) and `NewProposer`.
-/
module

public import Dsverify.Proof.raxos.Proposer.Propose
public import Dsverify.Proof.raxos.Proposer.Fetch

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open models_lab.pbcodec (PbCodec)
open raxos.replica.src

namespace prop

section run
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]

attribute [local instance] hyp.qpCodec

variable [gh : hyp.grpc.GrpcHyp qv.grpc] [rh : hyp.RandHyp GF]

theorem wp_runProposer (γ : QNames) (c : QConf) (k : Nat) (p : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proposerP γ c k p }}
      (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"runProposer")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as #Hprop
  ihave #Hprop' := Hprop
  iunfold proposerP at Hprop'
  icases Hprop' with ⟨%pv, %γ1, %γ2, %γ4, %γ5, %γ6, #Hp, %Hpv, -, -, #Hc1, #Hc2, #Hc4, #Hc5,
    #Hc6, -⟩
  iStructNamed Hp
  wp_auto
  ipersist prop
  wp_apply wp_fork $$ []
  · wp_auto
    wp_for_core
    wp_pures
    simp only [_root_.decide_true, ↓reduceIte]
    wp_auto_lc 6
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists FetchRequest, inferInstance, inferInstance, inferInstance, inferInstance,
        pv.proxyToProposerFetchChan', γ4
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hc4
      iapply bag_recv_au γ4 _ _ _ $$ [$Hlc1 $Hlc2] Hc4
      inext
      iintro %v Hv
      wp_auto
      wp_apply wp_handleFetchRequest γ c k p v $$ [$Hv] as %r Hr
      · iframe #
      wp_apply wp_bag_send γ5 _ r (fetchRespP γ) $$ [$Hr]
      · iframe #
      wp_for_post
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists ProposeRequest, inferInstance, inferInstance, inferInstance, inferInstance,
        pv.proxyToProposerChan', γ1
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hc1
      iapply bag_recv_au γ1 _ _ _ $$ [$Hlc3 $Hlc4] Hc1
      inext
      iintro %v Hv
      wp_auto
      wp_apply wp_handleProposeRequest γ c k p v $$ [$Hv] as %r Hr
      · iframe #
      wp_if_destruct <;>
      first
        | (wp_for_post; itrivial)
        | (wp_apply wp_bag_send γ2 _ r (proposeRespP γ k) $$ [$Hr]
           · iframe #
           wp_for_post
           itrivial)
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Decision, inferInstance, inferInstance, inferInstance, inferInstance,
        pv.proxyToProposerDecisionChan', γ6
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hc6
      iapply bag_recv_au γ6 _ _ _ $$ [$Hlc5 $Hlc6] Hc6
      inext
      iintro %v Hv
      wp_auto
      wp_apply wp_handleDecisionRequest γ c k p v $$ [$Hv]
      · iframe #
      wp_for_post
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
    done
  wp_end

theorem wp_NewProposer : NewProposer.spec (GF := GF) (hG := hG) := by
  intro γ c k i peers toProp fromProp toFetch fromFetch toDec γ1 γ2 γ4 γ5 γ6
  wp_start as ⟨%Hk, #Hconf, #Hpeers, #Hc1, #Hc2, #Hc4, #Hc5, #Hc6, #Hinv, -⟩
  simp only [callV, List.foldl]
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := GoSlice)) as %mp Hmp
  wp_apply time.wp_Now as %tn -
  ipersist pr
  ihave #Hpeers' := Hpeers
  iunfold peersP at Hpeers'
  icases Hpeers' with ⟨%ps, #Hps, %Hpsl, -⟩
  ihave %Hpl := ownSlice_len _ _ _ $$ Hps
  have Hcn := conf_n_sint c Hk.1
  have Hlen3 : peers.len = W64 c.n := by
    have h := Hpl.1; rw [Hpsl] at h
    exact w64_of_sint _ _ (by omega) (sint_of_nat _ _ h Hpl.2)
  imodintro
  iapply HΦ
  unfold proposerP
  iexists _, γ1, γ2, γ4, γ5, γ6
  iframe #
  ipureintro
  simp only [Hlen3]
  exact ⟨Hk.1, Hk.2.1, Hk.2.2, by simp⟩


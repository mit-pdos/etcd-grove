/-
Package `replica`: the recorder's gRPC service (`Recorder.serve`, `Recorder.NetworkInit`):
the `Consensus` descriptor meets `descOk` (the package fact `srcState` and the handlers'
`handlerOk`), and the serve loop (new server, registration, listen with retry, `Serve`) runs for
good.

Changed against the lab: the recorder listens at the wildcard `recLis k` (`0.0.0.0:port`, D21);
its protocols are `netProtos`' `recLisP` (`lisProto` of the wildcard, with the gRPC protocols of
its dialed address `recAddr k`): `Listen`'s atomic update comes from `listen_lis_au`, and the
`Serve` hypothesis takes the listener's `lisProto` (in place of the lab's `addrTok` (exclusive in
the lab, persistent in `Net/`), `nodeIp` and `grpcAddr`). The codec conjuncts are gone (protobuf
is a hypothesis).
-/
module

public import Dsverify.Proof.raxos.Replica.Fetch
public import Dsverify.Proof.raxos.Proposer.Strings
public import Dsverify.Proof.raxos.LibDeps
public import Perennial.Proof.time.Link
public import GooseLang.Ext.Net.Decide

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Perennial.raxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src
open hyp.grpc (handlerOk replyOk decOk descOk grpcAddr fullMethod GrpcVocab GrpcWorld)
open hyp.strconv (smallDigits decVal)

/-! ## Addresses and names -/

theorem digitChar_1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.2 rfl
theorem digitChar_2 : Nat.digitChar 2 = '2' := Nat.digitChar_eq_two.2 rfl
theorem digitChar_3 : Nat.digitChar 3 = '3' := Nat.digitChar_eq_three.2 rfl
theorem digitChar_4 : Nat.digitChar 4 = '4' := Nat.digitChar_eq_four.2 rfl
theorem digitChar_5 : Nat.digitChar 5 = '5' := Nat.digitChar_eq_five.2 rfl

theorem decStr_1 : decStr 1 = go!"1" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_lt_base (by omega), digitChar_1]
  decide +kernel
theorem decStr_2 : decStr 2 = go!"2" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_lt_base (by omega), digitChar_2]
  decide +kernel
theorem decStr_3 : decStr 3 = go!"3" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_lt_base (by omega), digitChar_3]
  decide +kernel
theorem decStr_4 : decStr 4 = go!"4" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_lt_base (by omega), digitChar_4]
  decide +kernel
theorem decStr_5 : decStr 5 = go!"5" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_lt_base (by omega), digitChar_5]
  decide +kernel

/-- A replica's name (`peersCfg`'s `Name`) is a small decimal (`Atoi`'s hypothesis). -/
theorem decStr_small (k : Nat) (hk : 1 ≤ k ∧ k ≤ 5) :
    smallDigits (decStr k) ∧ decVal (decStr k) = k := by
  obtain ⟨h1, h5⟩ := hk
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl | rfl | rfl
  · rw [decStr_1]; unfold smallDigits decVal; decide
  · rw [decStr_2]; unfold smallDigits decVal; decide
  · rw [decStr_3]; unfold smallDigits decVal; decide
  · rw [decStr_4]; unfold smallDigits decVal; decide
  · rw [decStr_5]; unfold smallDigits decVal; decide

theorem recLis_1 : recLis 1 = go!"0.0.0.0:7627" := by
  unfold recLis
  rw [prop.decStr_four _ 7 6 2 7 '7' '6' '2' '7' rfl (by omega) (by omega)
    (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)]
  decide
theorem recLis_2 : recLis 2 = go!"0.0.0.0:7628" := by
  unfold recLis
  rw [prop.decStr_four _ 7 6 2 8 '7' '6' '2' '8' rfl (by omega) (by omega)
    (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)]
  decide
theorem recLis_3 : recLis 3 = go!"0.0.0.0:7629" := by
  unfold recLis
  rw [prop.decStr_four _ 7 6 2 9 '7' '6' '2' '9' rfl (by omega) (by omega)
    (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)]
  decide
theorem recLis_4 : recLis 4 = go!"0.0.0.0:7630" := by
  unfold recLis
  rw [prop.decStr_four _ 7 6 3 0 '7' '6' '3' '0' rfl (by omega) (by omega)
    (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)]
  decide
theorem recLis_5 : recLis 5 = go!"0.0.0.0:7631" := by
  unfold recLis
  rw [prop.decStr_four _ 7 6 3 1 '7' '6' '3' '1' rfl (by omega) (by omega)
    (by omega) (by omega) (by simp) (by simp) (by simp) (by simp)]
  decide

/-- Recorder `r`'s dialed address is valid and its wildcard takes it. -/
theorem recAddr_ok (r : Nat) (hr : 1 ≤ r ∧ r ≤ 5) :
    addrOk (recAddr r) = true ∧ lisAccepts (recLis r) (recAddr r) := by
  rw [← lisAcceptsB_iff]
  obtain ⟨h1, h5⟩ := hr
  rcases (show r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 by omega) with rfl | rfl | rfl | rfl | rfl
  · rw [prop.recAddr_1, recLis_1]; decide
  · rw [prop.recAddr_2, recLis_2]; decide
  · rw [prop.recAddr_3, recLis_3]; decide
  · rw [prop.recAddr_4, recLis_4]; decide
  · rw [prop.recAddr_5, recLis_5]; decide

/-- Recorder `r`'s wildcard is a valid listening address. -/
theorem recLis_listenOk (r : Nat) (hr : 1 ≤ r ∧ r ≤ 5) : listenOk (recLis r) = true := by
  obtain ⟨h1, h5⟩ := hr
  rcases (show r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 by omega) with rfl | rfl | rfl | rfl | rfl
  · rw [recLis_1]; decide
  · rw [recLis_2]; decide
  · rw [recLis_3]; decide
  · rw [recLis_4]; decide
  · rw [recLis_5]; decide

section lis
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF] [π : NetProtoGS]

/-- A dialer's view of recorder `r`'s address (`lisProto_addr`). -/
theorem recLisP_grpcAddr (V : GrpcVocab GF) (W : GrpcWorld GF) (r : Nat) (hr : 1 ≤ r ∧ r ≤ 5) :
    recLisP V W r ⊢ grpcAddr V W (recAddr r) := by
  unfold recLisP
  iintro #⟨Hl, Hw⟩
  unfold grpcAddr
  iframe Hw
  iapply lisProto_addr _ _ _ _ (recAddr_ok r hr).1 (recAddr_ok r hr).2 $$ Hl

end lis

/-! ## The descriptor -/

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]

attribute [local instance] hyp.qpCodec

set_option goose.wp.extras true

instance descOk_discard_persistent (W : GrpcWorld GF) (a : GoString) (sd : Loc) (name : GoString)
    (ss : GoInterface) : Persistent (descOk qv.grpc W a sd .discard name ss) := by
  unfold descOk; infer_instance

/-- The package fact: the descriptor. -/
theorem src_state :
    isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ⊢ srcState := by
  iintro #H
  iapply isPkgInit_access $$ H

theorem consensus_descOk (γ : QNames) (k : Nat) (gc re : Loc) (hk : 1 ≤ k ∧ k ≤ 5) :
    isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
      gc.[GRPCConnection, go!"Recorder"] ↦□ re ∗ isRecorder γ k re ⊢
    descOk qv.grpc (world γ) (recAddr k) (globalAddr raxos.replica.src.Consensus_ServiceDesc)
      .discard go!"Consensus" (connIface gc) := by
  iintro ⟨#Hpkg, #Hgc, #Hre⟩
  ihave #Hs := src_state $$ Hpkg
  unfold srcState
  icases Hs with ⟨%sd, #Hsd, %Hsdf, #Hms⟩
  iStructNamed Hsd
  unfold descOk
  iexists sd.Methods', sd.Streams', _, ConsensusServer.ty, sd.Metadata'
  rw [← Hsdf.1, ← Hsdf.2.2]
  iframe #
  isplitr
  · ipureintro
    refine ⟨by rw [go.IsUnderlying.is_underlying (t := ConsensusServer.ty)]; rfl, _, rfl, ?_⟩
    go_type_set
  isplitr
  · ipureintro; exact Hsdf.2.1
  imodintro
  iintro %i %d %S %Hd
  obtain ⟨Hi, HS⟩ := Hd
  simp only [world, consensusMS, prop.recOfAddr_recAddr k hk] at HS
  rw [Hsdf.1] at HS
  rcases i with _ | _ | _ | i
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at Hi; subst Hi
    simp [fullMethod] at HS
    subst HS
    iapply esp_handlerOk γ k gc re $$ [$Hpkg $Hgc $Hre]
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hi; subst Hi
    simp [fullMethod] at HS
    subst HS
    iapply fetch_handlerOk γ k gc re $$ [$Hpkg $Hgc $Hre]
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at Hi; subst Hi
    simp [fullMethod] at HS
    subst HS
    iapply inform_handlerOk γ k gc re $$ [$Hpkg $Hgc $Hre]
  · simp at Hi

end proof

/-! ## The serve loop -/

section serve
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]

attribute [local instance] hyp.qpCodec

variable [gh : hyp.grpc.GrpcHyp qv.grpc]
variable [QpNetDeps GF]

set_option goose.wp.extras true

theorem wp_RegisterConsensusServer (s : Loc) (γs : GName) (a : GoString) (γ : QNames)
    (R : List GoString) (gc : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ qv.grpc.isServer s γs (world γ) a ∗
        qv.grpc.srvOwn γs R ∗ ⌜go!"Consensus" ∉ R⌝ ∗
        descOk qv.grpc (world γ) a (globalAddr raxos.replica.src.Consensus_ServiceDesc) .discard
          go!"Consensus" (connIface gc) }}
      (App (App (Val (@! raxos.replica.src.RegisterConsensusServer))
        (Val #(interface.mkOk (go.GoType.PointerType google_golang_org.grpc.Server.ty) #s)))
        (Val #(interface.mkOk (go.GoType.PointerType GRPCConnection.ty) #gc)))
    {{ RET #(); qv.grpc.srvOwn γs (go!"Consensus" :: R) ∗
        descOk qv.grpc (world γ) a (globalAddr raxos.replica.src.Consensus_ServiceDesc) .discard
          go!"Consensus" (connIface gc) }} := by
  wp_start as ⟨#Hsrv, Hown, %Hn, Hd⟩
  wp_auto
  wp_apply gh.RegisterService s γs (world γ) a R _ _ _ _
    $$ [$Hsrv $Hown $Hd] as ⟨Hown, Hd⟩
  · ipureintro; exact Hn
  iapply HΦ; iframe

theorem wp_serve (γ : QNames) (k : Nat) (r gc : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
        r.[Recorder, go!"address"] ↦□ recLis k ∗
        r.[Recorder, go!"connection"] ↦□ gc ∗ gc.[GRPCConnection, go!"Recorder"] ↦□ r ∗
        isRecorder γ k r ∗ recLisP qv.grpc (world γ) k }}
      (App (Val (r @!! go.GoType.PointerType Recorder.ty @!! go!"serve")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Haddr, #Hconn, #Hgc, #Hre, #Hlis⟩
  ihave %Hk : ⌜1 ≤ k ∧ k ≤ 5⌝ $$ []
  · iunfold isRecorder at Hre; icases Hre with ⟨%cb, %γs, %ch, %γc, %mu, -, -, -, -, -, -, -, -, %H⟩
    ipureintro; exact H
  ihave #Hdesc := consensus_descOk γ k gc r Hk $$ [$Hpkg $Hgc $Hre]
  iunfold recLisP at Hlis
  icases Hlis with ⟨#Hlp, #Hw⟩
  wp_auto
  wp_for
  wp_apply gh.NewServer (world γ) (recAddr k) slice.nil as %s %γs ⟨#Hsrv, Hown⟩
  · ipureintro; rfl
  wp_apply wp_RegisterConsensusServer s γs (recAddr k) γ [] gc $$ [$Hsrv $Hown $Hdesc]
    as ⟨Hown, -⟩
  · ipureintro; simp
  wp_apply QpNetDeps.listen go!"tcp" net.tcpNet_tcp (recLis k) as %li %err Hres
  · isplitr
    · ipureintro; exact recLis_listenOk k Hk
    iapply listen_lis_au $$ Hlp
  icases Hres with (⟨%Herr, %l, #Hli, Hl, Hon⟩ | ⟨%x, -, Herr⟩)
  · subst Herr
    wp_auto
    wp_apply gh.Serve s γs (world γ) (recAddr k) (recLis k) _ li l
      $$ [$Hsrv $Hown $Hli $Hl $Hon $Hlp $Hw] as %e -
    wp_for_post
    iframe
  · ihave %Hne := net.resErr_netErr _ _ _ _ _ _ _ $$ Herr
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    wp_apply time.wp_Sleep
    wp_for_post
    iframe

theorem wp_Recorder_NetworkInit (γ : QNames) (k : Nat) (r : Loc) (c0 : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
        r.[Recorder, go!"connection"] ↦ c0 ∗
        r.[Recorder, go!"address"] ↦□ recLis k ∗
        isRecorder γ k r ∗ recLisP qv.grpc (world γ) k }}
      (App (Val (r @!! go.GoType.PointerType Recorder.ty @!! go!"NetworkInit")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Hconn, #Haddr, #Hre, #Hlis⟩
  wp_auto
  irename «$r0» => Hgc
  generalize «$r0_ptr» = gc at *
  iStructNamed Hgc
  ipersist Recorder
  ipersist Hconn
  wp_apply wp_fork $$ []
  · wp_apply wp_serve γ k r gc $$ [$Haddr $Hconn $Recorder $Hre $Hlis]
    itrivial
  iapply HΦ; itrivial

end serve

end Perennial.raxos

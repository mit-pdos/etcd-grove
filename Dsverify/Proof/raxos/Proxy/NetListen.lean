/-
Package `proxy`: `connectionListener` (`proxynetwork.go`): the reader of a connection accepted on
the proxy's port. Each frame read is a registered batch carrying a ticket of the proxy; its credit
is minted (`credit_mint`) and the batch sent to the main loop (`incomingChan`, `incomingP`).
-/
module

public import Dsverify.Proof.raxos.Proxy.NetReader
public import Dsverify.Proof.raxos.Proxy.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open EtcdGrove (bufio.ownBufReader)
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions] [pb : hyp.PbHyp GF]
variable [net.Assumptions]
variable [QpBufioDeps GF]

attribute [local instance] HeapGS.goose_globalGS

/-- `credit_mint` at the full mask. -/
theorem mint_top (γ : QNames) (t : Ticket) (cid : Nat) (n : Nat) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ tixAt γ t cid n -∗ rdCtr γ cid n ={⊤}=∗
      rdCtr γ cid (n + 1) ∗ credit γ t :=
  credit_mint γ ⊤ (by solve_ndisj) t cid n

/-- `t.New()` on a `*ClientBatch`: a fresh `ClientBatch` as a `Serializable`. -/
theorem wp_CB_New (l : Loc) :
    {{ (True : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType raxos.proto.client.ClientBatch.ty @!! go!"New"))
        (Val #()))
    {{ (t : Loc), RET #(interface.mkOk (go.GoType.PointerType raxos.proto.client.ClientBatch.ty) #t);
        t ↦ zero_val raxos.proto.client.ClientBatch }} := by
  wp_start
  wp_auto
  wp_alloc t as Ht
  wp_auto
  iapply HΦ $$ Ht

theorem connectionListener_proof : connectionListener.spec (GF := GF) (hG := hG) := by
  intro γ c k pr br ri Pre E cid cl
  wp_start as ⟨#Hsh, %HPre, Hrd, Hctr⟩
  ihave ⟨#Hf, -, -, #Hl, #Hn⟩ := proxyShared_net γ c k pr $$ Hsh
  iunfold sharedNet at Hn
  icases Hn with ⟨%rm, %wm, %bm, %cm, %rt, %rp1, %cb0, %BM, %γw, %CM, %RT, -, -, -, -, -, -, -,
    -, -, -, -, -, #Hrt, #HRT, %HRT, #Hrp1⟩
  iunfold sharedLoop at Hl
  icases Hl with ⟨%_hs, #Hic, -⟩
  iunfold chanField at Hic
  icases Hic with ⟨%ich, %gi, #Hich, #Hbag⟩
  iunfold sharedFacts at Hf
  icases Hf with ⟨%hk, #Hcons, -⟩
  wp_auto
  ihave HI : (∃ (A : List Batch) (mt : w8) (e : GoInterface),
      "Hrd" ∷ bufio.ownBufReader br ri Pre (recvTokL cid true (proxyInProto γ k)) E
        (raxos.hs (21 + cl) ++ frs A) ∗
      "Hctr" ∷ rdCtr γ cid A.length ∗ "%HA" ∷ ⌜∀ b ∈ A, (encBatch b).length < 2 ^ 63⌝ ∗
      "msgType" ∷ msgType_ptr ↦ mt ∗ "err" ∷ err_ptr ↦ e : IProp GF) $$ [Hrd Hctr msgType err]
  · iexists [], _, _
    simp only [frs_nil, List.append_nil, List.length_nil]
    iframe
    ipureintro; simp
  wp_for HI
  wp_apply QpBufioDeps.readByte br ri Pre (recvTokL cid true (proxyInProto γ k)) E
    (raxos.hs (21 + cl) ++ frs A) $$ Hrd as %c %e1 Hres
  icases Hres with (⟨%He, Hrd⟩ | ⟨%He, -, -, Hrd⟩)
  · subst He
    ihave ⟨Hrd, #Hpp⟩ := net.connReader_proto br ri Pre cid true (proxyInProto γ k) E _ $$ Hrd
    wp_auto
    ihave %Hc := reader_code γ k (21 + cl) cid A c HA $$ Hpp
    subst Hc
    wp_apply wp_map_lookup2 $$ [HRT] as -
    · iexact HRT
    simp only [HRT, Option.getD_some, Option.isSome_some, decide_true]
    wp_auto
    ihave Hrp := Hrp1
    iStructNamed Hrp
    wp_auto
    wp_apply wp_CB_New cb0 as %t Ht
    ihave #Hlen := reader_len γ k (21 + cl) cid A HA
    wp_apply (unmarshal_bounded t br ri Pre (recvTokL cid true (proxyInProto γ k)) E _
        (protoPrefix (proxyInProto γ k) cid) (fun _ => inferInstance)
        (fun r => recvTokL_proto cid true _ r)
        (fun x y => protoPrefix_le (List.prefix_append x y))) $$ [Ht Hrd] as %e2 ⟨%data, Hrd, Hres⟩
    · iframe Ht Hrd Hlen
      ipureintro; exact HPre
    icases Hres with (%He | ⟨%bs, %b, ⟨%He, %Hdata, %Huniq, %Hbs⟩, Hrep⟩)
    · cases e2 with
      | nil => exact absurd rfl He
      | ok ie =>
        wp_auto
        wp_for_post
        iapply HΦ; itrivial
    subst He Hdata
    ihave ⟨Hrd, #Hpp2⟩ := net.connReader_proto br ri Pre cid true (proxyInProto γ k) E _ $$ Hrd
    wp_auto
    ihave ⟨%b', ⟨%Heb, %Hok, %Hlb, %Heq⟩, #Hreg, Htix⟩ :=
      reader_frame γ k (21 + cl) cid A bs HA Hbs $$ Hpp2
    obtain rfl : b = b' := Huniq b' Hok Heb
    ihave Hrep := Hrep $$ %(⟨b, Hok, Heb⟩ : ∃ b0, batchOk b0 ∧ encBatch b0 = bs)
    rw [Heq]
    icases Htix with ⟨%c', %j, Htix⟩
    imod (mint_top γ ((k : Int), c', j) cid A.length) $$ Hcons Htix Hctr
      with ⟨Hctr, Hcred⟩
    wp_apply wp_bag_send $$ [Hcred Hrep]
    · iframe Hbag
      iunfold incomingP
      iexists t, b, ((k : Int), c', j)
      iframe Hreg Hcred Hrep
      ipureintro; exact ⟨rfl, rfl, Hok, Hlb⟩
    wp_for_post
    iframe
    iexists A ++ [b], _, _
    rw [List.length_append, List.length_singleton]
    iframe
    ipureintro
    intro b0 hb0
    rcases List.mem_append.1 hb0 with h | h
    · exact HA b0 h
    · rw [List.mem_singleton.1 h]; exact Hlb
  · cases e1 with
    | nil => exact absurd rfl He
    | ok ie =>
      wp_auto
      wp_for_post
      iapply HΦ; itrivial

end proofs

end Perennial.raxos

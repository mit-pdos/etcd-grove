/-
**The watch laws of mvcc's API** (stage 2 of the mvcc API proof, the watch chain:
`notes/mvcc-api-risk.md`, M1; 2026-11-04), over the sealed definitions (`Api.lean`, over
`Api/StreamGhost.lean`). Lean-first (no Rocq counterpart).

- `wsRecv_ok.law_holds`: `wsRecv_ok.law`, a plain entailment (`wsRecv_okI`);
- `wsSentLb_zero.law_holds`;
- `wsChan_recv.law_holds`, over the channel invariant's receives (`watch_recv_au`,
  `watch_tryrecv_au_alt`, which move the API's view with the channel's received prefix and mint the
  receiver's lower bound, `chanApi_recv`), at a stream's names `wsAbsOf γw ch γc` (`wsChan_recvI`);
- the watch conjuncts of `persistent.law` (as instances) and of `excl.law`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchRecv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

instance isMvccWatchStream_persistent (ws : GoInterface) (γ : MvccName) (ι : WsName) :
    Persistent (isMvccWatchStream (GF := GF) ws γ ι) := by
  unfold isMvccWatchStream; infer_instance

instance wsSentLb_persistent (ι : WsName) (n : Nat) : Persistent (wsSentLb (GF := GF) ι n) := by
  unfold wsSentLb; exact wsSentLbI_persistent (GF := GF) (ι : WsAbs) n

instance mvccState_timeless (γ : MvccName) (σ : MvccState) :
    Timeless (mvccState (GF := GF) γ σ) := by
  unfold mvccState; infer_instance

instance wsState_timeless (ι : WsName) (S : StreamState) : Timeless (wsState (GF := GF) ι S) := by
  unfold wsState; exact wsStateI_timeless (GF := GF) (ι : WsAbs) S

instance wsRecv_timeless (ι : WsName) (rs : List WResp) : Timeless (wsRecv (GF := GF) ι rs) := by
  unfold wsRecv; exact wsRecvI_timeless (GF := GF) (ι : WsAbs) rs

theorem mvccState_excl (γ : MvccName) (σ σ' : MvccState) :
    mvccState (GF := GF) γ σ ∗ mvccState γ σ' ⊢ False := by
  unfold mvccState; exact mvccStateI_excl _ σ σ'

theorem wsState_excl (ι : WsName) (S S' : StreamState) :
    wsState (GF := GF) ι S ∗ wsState ι S' ⊢ False := by
  unfold wsState; exact wsStateI_excl _ S S'

theorem wsRecv_excl (ι : WsName) (rs rs' : List WResp) :
    wsRecv (GF := GF) ι rs ∗ wsRecv ι rs' ⊢ False := by
  unfold wsRecv; exact wsRecvI_excl _ rs rs'

/-- **`wsRecv_ok.law`**: a plain entailment, no invariant opened. -/
theorem wsRecv_ok.law_holds : wsRecv_ok.law (GF := GF) := by
  intro ws γ ι rs S σ
  unfold isMvccWatchStream wsRecv wsState mvccState
  iintro ⟨⟨%hst, -⟩, Hr, Hs, Hm⟩
  have hst' : (ι : WsAbs).st = (γ : StoreNames).api := hst
  rw [← hst']
  iapply wsRecv_okI ι rs S σ $$ [$Hr $Hs $Hm]

/-- **`wsSentLb_zero.law`.** -/
theorem wsSentLb_zero.law_holds : wsSentLb_zero.law (GF := GF) := by
  intro ι
  unfold wsSentLb
  exact wsSentLbI_zero ι

/-- A response received is, as the client sees it, the value received. -/
theorem respIs_wrespIs (v : WatchResponse) (r : RespM) :
    respIs (GF := GF) v r ⊢ wrespIs v r.toW := by
  unfold respIs wrespIs RespM.toW
  iintro H; iexact H

/-- The receive's result, as `wsChan_recv.law` gives it to the client. -/
theorem recvResult_api (γw : WsNames) (ch : Loc) (γc : WatchChanNames) (ms : List RespM)
    (l : List sent.SEv) (dec : GName → List (EvM → Bool)) (v : WatchResponse) (ok : Bool) :
    monoNatAuthOwn (GF := GF) γc.arx 1 0 ∗ logTok (wsAbsOf γw ch γc) l dec ∗
      monoNatLbOwn (wsAbsOf γw ch γc).ns (sent.nsCount l) ∗
      ⌜ms.map RespM.toW <+: sent.sendsOf l⌝ ∗ watchRecvResult γw ch γc ms v ok ⊢
      if ok then ∃ r : WResp, wsRecvI (wsAbsOf γw ch γc) (ms.map RespM.toW ++ [r]) ∗ wrespIs v r
      else wsRecvI (wsAbsOf γw ch γc) (ms.map RespM.toW) := by
  unfold watchRecvResult
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    iintro ⟨Hrx, #Htok, #Hns, %Hp, Hc⟩
    unfold watchConsumer wsRecvI
    rw [show (wsAbsOf γw ch γc).rcv = γc.arcv from rfl, show (wsAbsOf γw ch γc).crecv = γc.recv from rfl,
      show (wsAbsOf γw ch γc).rx = γc.arx from rfl]
    icases Hc with ⟨Hm, Hr⟩
    iexists l, dec
    iframe Hr Hrx Htok Hns
    isplitr
    · ipureintro; exact Hp
    iexists ms; iframe Hm; ipureintro; rfl
  · simp only [↓reduceIte]
    iintro ⟨Hrx, -, -, -, %r, Hc, #Hr, -, #Hlb, -⟩
    iexists r.toW
    ihave #Hw := respIs_wrespIs v r $$ Hr
    iframe Hw
    unfold watchConsumer wsRecvI apiRecvLb
    rw [show (wsAbsOf γw ch γc).rcv = γc.arcv from rfl, show (wsAbsOf γw ch γc).crecv = γc.recv from rfl,
      show (wsAbsOf γw ch γc).rx = γc.arx from rfl]
    icases Hc with ⟨Hm, Ha⟩
    icases Hlb with ⟨%l', %dec', #Htok', #Hns', %Hp'⟩
    have e : ms.map RespM.toW ++ [r.toW] = (ms ++ [r]).map RespM.toW := by simp
    rw [e]
    iexists l', dec'
    iframe Ha Hrx Htok' Hns'
    isplitr
    · ipureintro; exact Hp'
    iexists ms ++ [r]; iframe Hm; ipureintro; rfl

/-- **The receive law at a stream's names** (`wsChan_recv.law`'s body). -/
theorem wsChan_recvI (γw : WsNames) (ch : Loc) (γc : WatchChanNames)
    (hcap : 0 < sint.Z γc.ch.chanCap) :
    isChan (GF := GF) ch γc.ch WatchResponse ∗ inv watchN (watchChanInv γw ch γc) ⊢
    isChan ch γc.ch WatchResponse ∗
    □ (∀ (rs : List WResp) (Φ : WatchResponse → Bool → IProp GF),
      wsRecvI (wsAbsOf γw ch γc) rs -∗
      (∀ (v : WatchResponse) (ok : Bool),
        (if ok then ∃ r : WResp, wsRecvI (wsAbsOf γw ch γc) (rs ++ [r]) ∗ wrespIs v r
         else wsRecvI (wsAbsOf γw ch γc) rs) -∗ Φ v ok) -∗
      recvAu γc.ch WatchResponse Φ) ∗
    □ (∀ (rs : List WResp) (n : Nat) (Φ : WatchResponse → Bool → IProp GF) (Ψ : IProp GF),
      wsRecvI (wsAbsOf γw ch γc) rs -∗ wsSentLbI (wsAbsOf γw ch γc) n -∗
      ((∀ (v : WatchResponse) (ok : Bool),
          (if ok then ∃ r : WResp, wsRecvI (wsAbsOf γw ch γc) (rs ++ [r]) ∗ wrespIs v r
           else wsRecvI (wsAbsOf γw ch γc) rs) -∗ Φ v ok) ∧
        (wsRecvI (wsAbsOf γw ch γc) rs -∗ ⌜n ≤ rs.length⌝ -∗ Ψ)) -∗
      nonblockingRecvAuAlt γc.ch WatchResponse Φ Ψ) := by
  iintro ⟨#Hch, #Hinv⟩
  iframe Hch
  isplitr
  · iintro !> %rs %Φ Hw HΦ
    unfold wsRecvI
    rw [show (wsAbsOf γw ch γc).rcv = γc.arcv from rfl, show (wsAbsOf γw ch γc).crecv = γc.recv from rfl,
      show (wsAbsOf γw ch γc).rx = γc.arx from rfl]
    icases Hw with ⟨%l, %dec, Hr, Hrx, #Htok, #Hns, %Hpre, %ms, Hm, %Hms⟩
    subst Hms
    iapply watch_recv_au γw ch γc ms Φ $$ Hinv [Hm Hr]
    · unfold watchConsumer; iframe Hm Hr
    iintro %v %ok Hres
    iapply HΦ
    ihave H := recvResult_api γw ch γc ms l dec v ok $$ [$Hrx $Htok $Hns $Hres]
    · ipureintro; exact Hpre
    unfold wsRecvI
    rw [show (wsAbsOf γw ch γc).rcv = γc.arcv from rfl, show (wsAbsOf γw ch γc).crecv = γc.recv from rfl,
      show (wsAbsOf γw ch γc).rx = γc.arx from rfl]
    iexact H
  · iintro !> %rs %n %Φ %Ψ Hw #Hn HK
    unfold wsRecvI
    rw [show (wsAbsOf γw ch γc).rcv = γc.arcv from rfl, show (wsAbsOf γw ch γc).crecv = γc.recv from rfl,
      show (wsAbsOf γw ch γc).rx = γc.arx from rfl]
    icases Hw with ⟨%l, %dec, Hr, Hrx, #Htok, #Hns, %Hpre, %ms, Hm, %Hms⟩
    subst Hms
    have key := watch_tryrecv_au_alt (GF := GF) γw ch γc ms [] n Φ Ψ hcap
    unfold nonblockingRecvAuAlt at key ⊢
    imod monoListLbOwn_nil (GF := GF) (A := RespM) γc.sentl with #Hl0
    iapply key $$ Hinv [Hm Hr] [] Hn
    · unfold watchConsumer; iframe Hm Hr
    · unfold chanSentLb; iexact Hl0
    isplit
    · iintro %v %ok Hres
      icases HK with ⟨HΦ, -⟩
      iapply HΦ
      ihave H := recvResult_api γw ch γc ms l dec v ok $$ [$Hrx $Htok $Hns $Hres]
      · ipureintro; exact Hpre
      unfold wsRecvI
      rw [show (wsAbsOf γw ch γc).rcv = γc.arcv from rfl,
        show (wsAbsOf γw ch γc).crecv = γc.recv from rfl, show (wsAbsOf γw ch γc).rx = γc.arx from rfl]
      iexact H
    · iintro Hc %Hle -
      icases HK with ⟨-, HΨ⟩
      unfold watchConsumer
      icases Hc with ⟨Hm, Hr⟩
      iapply HΨ $$ [Hm Hr Hrx]
      · iexists l, dec
        iframe Hr Hrx Htok Hns
        isplitr
        · ipureintro; exact Hpre
        iexists ms; iframe Hm; ipureintro; rfl
      · ipureintro; simpa using Hle.2

/-- **`wsChan_recv.law`**: the stream's channel and its invariant, at the stream's names. -/
theorem wsChan_recv.law_holds : wsChan_recv.law (GF := GF) := by
  intro ws γ ι
  unfold isMvccWatchStream isMvccWatchStreamRest wsChanOf wsChanNames wsRecv wsSentLb
  iintro ⟨%hst, #⟨%γw, %γc, %w, %s, %st, %γo, %γp, %hι, #Hch, #Hinv, -, -, -, -⟩⟩
  obtain ⟨hι, -, hcap, -⟩ := hι
  have key : ∀ (ι : WsAbs), ι = wsAbsOf γw ι.ch γc →
      isChan (GF := GF) ι.ch γc.ch WatchResponse ∗ inv watchN (watchChanInv γw ι.ch γc) ⊢
      isChan ι.ch ι.chn WatchResponse ∗
      □ (∀ (rs : List WResp) (Φ : WatchResponse → Bool → IProp GF),
        wsRecvI ι rs -∗
        (∀ (v : WatchResponse) (ok : Bool),
          (if ok then ∃ r : WResp, wsRecvI ι (rs ++ [r]) ∗ wrespIs v r else wsRecvI ι rs) -∗
            Φ v ok) -∗
        recvAu ι.chn WatchResponse Φ) ∗
      □ (∀ (rs : List WResp) (n : Nat) (Φ : WatchResponse → Bool → IProp GF) (Ψ : IProp GF),
        wsRecvI ι rs -∗ wsSentLbI ι n -∗
        ((∀ (v : WatchResponse) (ok : Bool),
            (if ok then ∃ r : WResp, wsRecvI ι (rs ++ [r]) ∗ wrespIs v r else wsRecvI ι rs) -∗
              Φ v ok) ∧
          (wsRecvI ι rs -∗ ⌜n ≤ rs.length⌝ -∗ Ψ)) -∗
        nonblockingRecvAuAlt ι.chn WatchResponse Φ Ψ) := by
    intro ι h
    obtain ⟨st, ev, ns, rcv, rx, c, chn, crecv, cl⟩ := ι
    simp only [wsAbsOf, WsAbs.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, -, rfl, rfl, rfl⟩ := h
    exact wsChan_recvI γw c γc hcap
  iapply key (ι : WsAbs) hι $$ [$Hch $Hinv]

end laws

end api
end mvcc
end EtcdGrove
end Perennial

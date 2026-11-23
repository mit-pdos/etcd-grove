/-
The proof of `Server.ServeCodec` (`Net/Spec/net/rpc/Server__ServeCodec.lean`). `sending` is a new
mutex over `srvSendInv` (nothing written, no answer recorded); `wg` a new thread-token join
(`sync.tokJoin` at `srvWgN`, no lending: `lendLaw_false`). **The loop's invariant**: the reader's
resources (`rdrOwn`), the join's adder, the reader's thread token. **An iteration**
(`readRequest`): a read failure ends the loop; an error with the request taken is answered at once
(`sendResponse`, with `errCont`'s `Φ [] msg` for the error's message, not empty) and the request
freed; a request ready to run is added to the join (`Add(1)` with the thread token) and runs in a
goroutine (`service.call`, `wp_fork_tok_self`: the token of the `go` statement comes back to the
reader, the goroutine exits with the slot's). **After the loop**: `Wait`, then the codec's `Close`
(`close_au`, the end's `connIs` from its tokens).
-/
module

public import Net.Spec.net.rpc.Server__ServeCodec
public import Net.Spec.net.rpc.Server__readRequest
public import Net.Spec.net.rpc.Server__sendResponse
public import Net.Spec.net.rpc.Server__freeRequest
public import Net.Spec.net.rpc.service__call
public import Net.Spec.net.rpc.serverCodec__Close
public import Net.Proof.net.rpc.ServerGhost
public import Perennial.Proof.sync.Results

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [sync.Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem Server.ServeCodec.wp_proof
    (wp_readRequest : Server.readRequest.spec (GF := GF) (hG := hG))
    (wp_sendResponse : Server.sendResponse.spec (GF := GF) (hG := hG))
    (wp_freeRequest : Server.freeRequest.spec (GF := GF) (hG := hG))
    (wp_call : service.call.spec (GF := GF) (hG := hG))
    (wp_Close : serverCodec.Close.spec (GF := GF) (hG := hG)) :
    Server.ServeCodec.spec (GF := GF) (hG := hG) := by
  intro s γs C W a sc t cn la ra
  wp_start as ⟨%Hb, #Hsrv, #Hserves, #Henv, #Hset, #Hsc, Hown, Htok⟩
  ihave #Hsrv' := Hsrv
  iunfold isServer at Hsrv'
  icases Hsrv' with ⟨#Hsync, -⟩
  iunfold srvCodecOwn at Hown
  icases Hown with ⟨Hwerr, Hrerr, Hclosed, Hacc⟩
  iunfold rpcAccepted at Hacc
  icases Hacc with ⟨%w, %Hw, Hsend, Hrecv, Hfresh⟩
  ihave #Hci := sendTok_connIs $$ Hsend
  icases recvTok_keep_sentLb (Gg := hG.goose_globalGS) cn true false rfl _ _ $$ Hrecv
    with ⟨Hrecv, #Hsl⟩
  ihave #Henv0 := Henv
  iunfold srvEnv at Henv0
  icases Henv0 with ⟨#Hcli, #Hir⟩
  ihave #Hcli' := Hcli
  iunfold cliEnv at Hcli'
  icases Hcli' with ⟨%eof, %ueof, %ed, #Hio, -, #Heof, #Hueof, #Hed, #HefV, #HesV, #Hdbg⟩
  ihave #Hsc0 := Hsc
  iunfold srvCodecAt at Hsc0
  icases Hsc0 with ⟨#Hrwc, #Hconn⟩
  wp_auto
  irename : (_ ↦ (_root_.Perennial.zero_val sync.Mutex) : IProp GF) => Hmu0
  irename «$r0» => Hwg0
  generalize «$r0_ptr» = wgl at *
  imod sync.init_Mutex (srvSendInv W a cn sc) ⊤ _ $$ Hmu0 [Hwerr Hsend] with #Hmu
  · inext
    iunfold srvSendInv
    iexists interface.nil, w, []
    iframe Hwerr Hsend Hsl
    isplitr
    · iunfold ansRec; ileft; ipureintro; rfl
    ipureintro
    exact ⟨by simp, by simpa [respsWire, framesOf] using Hw, fun _ => Or.inr ⟨rfl, Hw⟩⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hwg0 with ⟨Hwg0, %Hwgnn⟩
  imod sync.init_WaitGroup (srvWgN.@"wg") wgl $$ Hwg0 with ⟨%γwg, #Hiswg, Hctr, Hwait⟩
  ihave #Hlaw := sync.tokJoin.lendLaw_false (GF := GF) srvWgN
  imod sync.tokJoin.init srvWgN iprop(False) wgl γwg ⊤ Hb $$ [$Hiswg $Hctr $Hwait $Hlaw] with Hadd
  ihave HI : (∃ (n : Nat) (Pw : IProp GF), "Hrd" ∷ rdrOwn W a cn sc ∗
      "Hadd" ∷ sync.tokJoin.ownAdder srvWgN iprop(False) wgl n Pw ∗
      "Htok" ∷ threadTok : IProp GF) $$ [Hrerr Hrecv Hfresh Hadd Htok]
  · iexists 0, iprop(True)
    iframe Hadd Htok
    iunfold rdrOwn
    iexists _
    iframe Hrerr
    ileft
    isplitr
    · ipureintro; rfl
    iexists [], 0
    isplitl
    · iunfold readerSt
      rw [framesOf_nil, List.append_nil]
      iframe Hrecv
      isplitr
      · ipureintro; simp
      ileft
      iframe Hfresh
      ipureintro; rfl
    ipureintro; rfl
  wp_for HI
  wp_apply wp_readRequest s γs C W a sc t cn la ra $$ [$Hsrv $Hserves $Henv $Hsc $Hrd]
    as %svc %mt %req %argv %replyv %keep %err Hres
  icases Hres with (⟨%Hk, %He⟩ | ⟨%Hk, %k, %r, %Φc, Hr, Hpend, Hrd, Hcase⟩)
  · -- the header's read failed: the loop ends
    subst Hk
    cases err with
    | nil => exact absurd rfl He
    | ok e =>
    wp_auto
    wp_for_post
    wp_apply (sync.tokJoin.WaitGroup.wp_Wait srvWgN iprop(False) wgl n Pw)
      $$ [$Hsync $Hadd] as ⟨-, -⟩
    wp_apply wp_Close sc t cn true a la ra false (fun _ => iprop(True)) $$ [$Hrwc $Hconn $Hclosed]
      as %err2 -
    · simp only [Bool.false_eq_true, ite_false]
      imod close_au (Gg := hG.goose_globalGS) cn true $$ Hci with ⟨%st, %d, Hst, Hd, Hk⟩
      imodintro
      iexists st, d
      iframe Hst Hd
      iintro %res %st' %d' %Hco Hst' Hd'
      imod Hk $$ %res %st' %d' %Hco Hst' Hd' with -
      imodintro
      itrivial
    iapply HΦ
    iexact Htok
  subst Hk
  icases Hcase with (⟨%He, Hcall⟩ | ⟨%He, #HeNE, Hcont⟩)
  · -- a request ready to run, in a goroutine of its own
    subst He
    wp_auto
    wp_apply (sync.tokJoin.WaitGroup.wp_Add iprop(True) srvWgN iprop(False) wgl n Pw)
      $$ [$Hsync $Hadd $Htok] as ⟨Hadd, Hdone⟩
    wp_bind (Fork _)
    iapply wp_fork_tok_self $$ [Hdone Hr Hpend Hcall]
    · inext
      wp_apply wp_call svc s γs C W a sc t cn la ra _ wgl mt req _ argv replyv k Φc
        $$ [$Hsrv $Henv $Hset $Hsc $Hmu $Hr $Hpend $Hcall $Hdone] as Htok
      · ipureintro; exact ⟨rfl, Hwgnn⟩
      iframe Htok
      ipureintro; exact isPanic_intoVal ()
    inext
    iintro Htok
    wp_auto
    wp_for_post
    iframe
    iexists n + 1, iprop(Pw ∗ True)
    iframe Hrd Hadd Htok
  · -- an error answered at once
    cases err with
    | nil => exact absurd rfl He
    | ok e =>
    wp_auto
    by_cases hreq : req = null
    · rw [decide_eq_true hreq]
      wp_auto
      wp_for_post
      iframe
      iexists n, Pw
      iframe Hrd Hadd Htok
    rw [decide_eq_false hreq]
    wp_auto
    ihave #HeNE' := HeNE
    iunfold errNE at HeNE'
    icases HeNE' with ⟨%ei, %Hei, -, #HW⟩
    cases Hei
    wp_bind (App (Val #(methods _ go!"Error" _)) (Val #()))
    iapply HW
    inext
    iintro %msg %hmsg
    iapply fupd_wp
    iunfold errCont at Hcont
    imod Hcont $$ %msg %hmsg with HΦa
    imodintro
    wp_auto
    wp_apply wp_sendResponse s γs C W a sc t cn la ra _ req _
        (interface.mkOk (go.GoType.StructType []) #()) msg k Φc
        $$ [$Hsrv $Henv $Hset $Hsc $Hmu $Hr $Hpend HΦa] as Hr
    · isplitr
      · ipureintro; rfl
      iunfold ansRes
      simp only [hmsg, ↓reduceIte]
      iexact HΦa
    wp_apply wp_freeRequest s γs req _ $$ [$Hsrv $Hr]
    wp_for_post
    iframe
    iexists n, Pw
    iframe Hrd Hadd Htok

end proof

end net.rpc
end Perennial

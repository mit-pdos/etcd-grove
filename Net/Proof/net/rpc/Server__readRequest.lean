/-
The proof of `Server.readRequest` (`Net/Spec/net/rpc/Server__readRequest.lean`): the header
(`readRequestHeader`); after an error with the request taken, its body discarded
(`ReadRequestBody(nil)`: the reader advances by the frame, or its read fails, `rerr` then holding
the error); otherwise the method's `NewArg` (`methodOk`: an argument and its decoding, `argDec`,
of the argument bytes of a deposit), the deposit's decoding (the deposit kept), the body decoded
into it (`ReadRequestBody` guarded by `req_guard`: the frame read is the request's argument bytes;
`req_body` again after the read), and on a decoding
the deposit and the decoding turned into the call obligation, whose `NewReply` runs here
(`callObl`); a body that does not read or decode is an error (`rdErr`, `decErr`: messages not
empty) with the deposit spent on `errOk` (`errCont`). Two later credits: the body's protocol fact.
-/
module

public import Net.Spec.net.rpc.Server__readRequest
public import Net.Spec.net.rpc.Server__readRequestHeader
public import Net.Spec.net.rpc.serverCodec__ReadRequestBody
public import Net.Proof.net.rpc.ServerGhost

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
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A decoding error has a message not empty (`errNE`). -/
theorem errNE_decErr (err : GoInterface) : decErr (GF := GF) err ⊢ errNE err := by
  iunfold decErr
  iintro ⟨%x, %msg, ⟨%He, %Hm⟩, #H⟩
  subst He
  iapply errNE_errorString x msg Hm $$ H

/-- The reader after a request's body frame `pl`: back at the top of its loop. -/
theorem rdr_adv (W : RpcWorld GF) (a : GoString) (cn : Nat) (γ : RpcConnNames) (k : Nat)
    (ps : List (List w8)) (h pl : List w8) (hps : ps.length = 2 * k)
    (hb : ∀ q ∈ ps, q.length < 2 ^ 63) (hh : h.length < 2 ^ 63) (hpl : pl.length < 2 ^ 63) :
    recvTok (Gg := hG.goose_globalGS) cn true (reqProto (Gg := hG.goose_globalGS) W a)
        (W.hs a ++ framesOf (ps ++ [h]) ++ frameOf pl) ∗
      isRpcConn (Gg := hG.goose_globalGS) W a cn γ ∗ ghostVar γ.ctr (1 : Qp).half (k + 1) ⊢
    ∃ (ps' : List (List w8)) (k' : Nat), readerSt W a cn ps' k' ∗ ⌜ps'.length = 2 * k'⌝ := by
  iintro ⟨Hrecv, #Hrpc, Hctr⟩
  iexists ps ++ [h, pl], k + 1
  isplitl
  · iunfold readerSt
    rw [show ps ++ [h, pl] = (ps ++ [h]) ++ [pl] by simp, framesOf_append (ps ++ [h]) [pl],
      framesOf_cons, framesOf_nil, List.append_nil, ← List.append_assoc]
    iframe Hrecv
    isplitr
    · ipureintro
      intro q hq
      simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with (hq | rfl) | rfl
      · exact hb q hq
      · exact hh
      · exact hpl
    iright
    iexists γ
    iframe Hrpc Hctr
  · ipureintro; simp; omega

theorem Server.readRequest.wp_proof
    (wp_readRequestHeader : Server.readRequestHeader.spec (GF := GF) (hG := hG))
    (wp_ReadRequestBody : serverCodec.ReadRequestBody.spec (GF := GF) (hG := hG)) :
    Server.readRequest.spec (GF := GF) (hG := hG) := by
  intro s γs C W a sc t cn la ra
  wp_start as ⟨#Hsrv, #Hserves, #Henv, #Hsc, Hrd⟩
  ihave #Henv0 := Henv
  iunfold srvEnv at Henv0
  icases Henv0 with ⟨#Hcli, -⟩
  ihave #Hcli' := Hcli
  iunfold cliEnv at Hcli'
  icases Hcli' with ⟨%eof, %ueof, %ed, #Hio, #Hsync, #Heof, #Hueof, #Hed, #HefV, #HesV, #Hdbg⟩
  ihave #HefV' := HefV
  iunfold errors.newVar at HefV'
  icases HefV' with ⟨%xf, #Hef, -⟩
  ihave #Hsc0 := Hsc
  iunfold srvCodecAt at Hsc0
  icases Hsc0 with ⟨#Hrwc, #Hconn⟩
  wp_auto
  wp_apply wp_readRequestHeader s γs C W a sc t cn la ra $$ [$Hsrv $Hserves $Henv $Hsc $Hrd]
    as %svc %mt %req %keep %err Hres
  icases Hres with (⟨%Hk, %He⟩ | ⟨%Hk, %k, %r, %Φc, Hr, Hrerr, Hmid, Hpend, Hcase⟩)
  · -- the header's read failed
    subst Hk
    cases err with
    | nil => exact absurd rfl He
    | ok e =>
    wp_auto
    iapply HΦ
    ileft
    ipureintro; exact ⟨rfl, He⟩
  subst Hk
  iunfold rdrMid at Hmid
  icases Hmid with ⟨%γ, %L, %ps, Hrecv, #Hrpc, #Hlb, Hctr, ⟨%HLr, %Hps, %Hb, %Hrok⟩⟩
  have hh : (reqHdr (W64 k) r.sm).length < 2 ^ 63 := by
    rw [reqHdr_length]; unfold reqOk at Hrok; omega
  ihave HrL : recvTokL (Gg := hG.goose_globalGS) cn true (reqProto (Gg := hG.goose_globalGS) W a)
      (W.hs a ++ framesOf (ps ++ [reqHdr (W64 k) r.sm]) ++ []) $$ [Hrecv]
  · rw [List.append_nil]; iapply recvTok_L $$ Hrecv
  ihave #Hacc := rd_acc_srv W a cn (W.hs a ++ framesOf (ps ++ [reqHdr (W64 k) r.sm]))
  icases Hcase with (⟨%He, %S, %m, %rcvr, HS, #HerrOk, #Hrcvr, #Hmt⟩ | ⟨%He, #HeNE, Hcont⟩)
  rotate_left
  · -- an error with the request taken: its body discarded
    cases err with
    | nil => exact absurd rfl He
    | ok e =>
    wp_auto_lc 1
    ihave #Hg0 := guard_true (fun got => recvTokL (Gg := hG.goose_globalGS) cn true
      (reqProto (Gg := hG.goose_globalGS) W a) (W.hs a ++ framesOf (ps ++ [reqHdr (W64 k) r.sm]) ++ got))
    wp_apply +noauto wp_ReadRequestBody sc t cn true a la ra interface.nil interface.nil C iprop(True)
        (fun _ => iprop(True)) (fun _ _ => iprop(True))
        (fun got => recvTokL (Gg := hG.goose_globalGS) cn true
          (reqProto (Gg := hG.goose_globalGS) W a) (W.hs a ++ framesOf (ps ++ [reqHdr (W64 k) r.sm]) ++ got))
        eof ueof ed _ $$ [$Hrwc $Hconn $Hio $Heof $Hueof $Hed $Hef $HefV $HrL $Hg0 $Hrerr $Hacc]
      as %err1 (⟨⟨%Hc, -⟩, -⟩ | ⟨-, %got, HP, Hres⟩)
    · iunfold bodyDecG; itrivial
    · exact absurd rfl Hc
    ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn true _ _ $$ HP
    iapply fupd_wp
    imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HrT with HrT
    imodintro
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists k, r, Φc
    iframe Hr Hpend
    isplitr [Hcont]
    · icases Hres with (⟨%pl, ⟨%Hgot, %Hpl⟩, -, Hrerr⟩ | ⟨%Hne1, -, #HE1, Hrerr⟩)
      · subst Hgot
        iunfold rdrOwn
        iexists _
        iframe Hrerr
        ileft
        isplitr
        · ipureintro; rfl
        iapply rdr_adv W a cn γ k ps _ pl Hps Hb hh (by unfold maxFrameN at Hpl; omega)
          $$ [$HrT $Hrpc $Hctr]
      · iunfold rdrOwn
        iexists _
        iframe Hrerr
        iright
        isplitr
        · ipureintro; exact Hne1
        isplitr
        · iapply rdErr_read la ra eof ueof ed _ true got err1 $$ [$HefV $Hef $Hio $Heof $Hueof $HE1]
        iexists _
        iexact HrT
    iright
    isplitr
    · ipureintro; exact He
    iframe HeNE Hcont
  -- the method found: its argument, the body decoded into it, its reply
  subst He
  iunfold methodTypeIs at Hmt
  icases Hmt with ⟨%mm, #Hm, #Hmok, #Hmmu⟩
  ihave #Hmok' := Hmok
  iunfold methodOk at Hmok'
  icases Hmok' with ⟨%v, #Hv, #Hnew⟩
  ihave #Hv2 := Hv
  iStructNamed Hv2
  wp_auto
  wp_bind (App (Val #v.NewArg') (Val #()))
  iapply Hnew
  inext
  iintro %argv %D %Θ %Hargv #Hdec HD Hobl
  cases argv with
  | nil => exact absurd rfl Hargv
  | ok av =>
  wp_auto_lc 1
  ihave #HerrOk' := HerrOk
  iunfold errOk at HerrOk'
  -- the decoding of the request's argument bytes, from its deposit (kept), guarded by the body read
  iunfold argDec at Hdec
  icases Hdec with ⟨#Hset, #Hd⟩
  icases Hd $$ HD %r.body %Φc HS with ⟨HS, Hdc0⟩
  ihave #Hguard := req_guard W a cn γ L r ps k _ HLr Hps Hb hh $$ [$Hrpc $Hlb]
  ihave #Hdec3 : bodyDecG C (interface.ok av) (C.dec r.body (interface.ok av) (Θ r.body))
      (fun pl => iprop(⌜pl = r.body⌝)) Θ $$ []
  · simp only [bodyDecG]
    iframe Hset
    imodintro
    iintro Hdc %pl %Hplr
    subst Hplr
    iexact Hdc
  wp_apply +noauto wp_ReadRequestBody sc t cn true a la ra (interface.ok av) interface.nil C
      (C.dec r.body (interface.ok av) (Θ r.body)) (fun pl => iprop(⌜pl = r.body⌝)) Θ
      (fun got => recvTokL (Gg := hG.goose_globalGS) cn true
        (reqProto (Gg := hG.goose_globalGS) W a) (W.hs a ++ framesOf (ps ++ [reqHdr (W64 k) r.sm]) ++ got))
      eof ueof ed _ $$ [$Hrwc $Hconn $Hio $Heof $Hueof $Hed $Hef $HefV $Hdec3 $Hdc0 $HrL $Hguard
        $Hrerr $Hacc]
    as %err1 (⟨⟨%Hc, -⟩, -⟩ | ⟨-, %got, HP, Hres⟩)
  · exact absurd rfl Hc
  ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn true _ _ $$ HP
  iapply fupd_wp
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HrT with HrT
  imodintro
  icases Hres with (⟨%pl, ⟨%Hgot, %Hpl⟩, Hbr, Hrerr⟩ | ⟨%Hne1, -, #HE1, Hrerr⟩)
  rotate_left
  · -- the body's read failed
    cases err1 with
    | nil => exact absurd rfl Hne1
    | ok e1 =>
    wp_auto
    ihave #Hre := rdErr_read la ra eof ueof ed _ true got (interface.ok e1)
      $$ [$HefV $Hef $Hio $Heof $Hueof $HE1]
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists k, r, Φc
    iframe Hr Hpend
    isplitr [HS]
    · iunfold rdrOwn
      iexists _
      iframe Hrerr
      iright
      isplitr
      · ipureintro; exact Hne1
      iframe Hre
      iexists _
      iexact HrT
    iright
    isplitr
    · ipureintro; exact Hne1
    isplitr
    · iunfold rdErr at Hre
      icases Hre with ⟨#Hn, -⟩
      iexact Hn
    iunfold errCont
    iintro %msg %hmsg
    iapply HerrOk' $$ %m %r.body %Φc %msg %hmsg HS
  subst Hgot
  have hpl : pl.length < 2 ^ 63 := by unfold maxFrameN at Hpl; omega
  have hfr : W.hs a ++ framesOf (ps ++ [reqHdr (W64 k) r.sm]) ++ frameOf pl =
      W.hs a ++ framesOf (ps ++ [reqHdr (W64 k) r.sm] ++ [pl]) := by
    rw [framesOf_append (ps ++ [reqHdr (W64 k) r.sm]) [pl], framesOf_cons, framesOf_nil,
      List.append_nil, List.append_assoc]
  icases recvTok_proto (Gg := hG.goose_globalGS) cn true _ _ $$ HrT with ⟨HrT, #Hpp⟩
  rw [hfr]
  ihave %Hbody := req_body W a cn γ L r ps k _ pl HLr Hps Hb hh hpl $$ [$Hrpc $Hlb $Hpp]
  rw [← hfr]
  ihave Hown : rdrOwn W a cn sc $$ [HrT Hctr Hrerr]
  · iunfold rdrOwn
    iexists _
    iframe Hrerr
    ileft
    isplitr
    · ipureintro; rfl
    iapply rdr_adv W a cn γ k ps _ pl Hps Hb hh hpl $$ [$HrT $Hrpc $Hctr]
  subst Hbody
  iunfold bodyRes at Hbr
  icases Hbr with ⟨%ok, %Hok, HΘ, Hdc⟩
  cases ok
  · -- not decoded
    simp only [Bool.false_eq_true, ite_false]
    have Hne1 : err1 ≠ interface.nil := fun h => absurd (Hok.1 h) (by simp)
    cases err1 with
    | nil => exact absurd rfl Hne1
    | ok e1 =>
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists k, r, Φc
    iframe Hr Hpend Hown
    iright
    isplitr
    · ipureintro; exact Hne1
    isplitl [Hdc]
    · iapply errNE_decErr $$ Hdc
    iunfold errCont
    iintro %msg %hmsg
    iapply HerrOk' $$ %m %r.body %Φc %msg %hmsg HS
  · -- decoded: the reply, and the call obligation
    have He1 : err1 = interface.nil := Hok.2 rfl
    subst He1
    wp_auto
    ihave Hcobl := Hobl $$ %r.body %Φc HS HΘ
    iunfold callObl at Hcobl
    wp_bind (App (Val #v.NewReply') (Val #()))
    iapply wp_wand $$ Hcobl
    iintro %rr ⟨%replyv, %Hrr, Hcall⟩
    subst Hrr
    wp_auto
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iexists k, r, Φc
    iframe Hr Hpend Hown
    ileft
    isplitr
    · ipureintro; rfl
    iunfold callReady
    iexists rcvr, mm, v
    iframe Hrcvr Hm Hv Hmmu Hcall

end proof

end net.rpc
end Perennial

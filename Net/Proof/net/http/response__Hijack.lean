/-
The proof of `response.Hijack` (`Net/Spec/net/http/response__Hijack.lean`): `handlerDone` false,
`disableWriteContinue` returns at once (no expect-continue reader), nothing written; under
`c.mu` (`connMuInv`: the flag false, by the serving thread's half) `hijackLocked`, then the flag's
ghost variable set with it; the response's writer put back (`putBufioWriter`).
-/
module

public import Net.Spec.net.http.response__Hijack
public import Net.Spec.net.http.conn__hijackLocked
public import Net.Proof.net.http.ServerConnLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS] [net.Assumptions] [field_sem : net.FieldAssumptions]
variable [bufio_sem : bufio.Assumptions]

/-- `w.disableWriteContinue(skip)` with no expect-continue reader. -/
theorem wp_disableWriteContinue (w : Loc) (skip : Bool) :
    {{ (structFieldRef net.http.response go!"ecReader" w ↦ (null : Loc) : IProp GF) }}
      (App (Val (w @!! go.GoType.PointerType net.http.response.ty @!! go!"disableWriteContinue"))
        (Val #skip))
    {{ RET #(); structFieldRef net.http.response go!"ecReader" w ↦ (null : Loc) }} := by
  wp_start as He
  wp_auto
  iapply HΦ $$ He

theorem wp_hijack
    (wp_hijackLocked : conn.hijackLocked.spec (GF := GF) (hG := hG))
    (wp_Reset : EtcdGrove.bufio.Writer.Reset.spec (GF := GF) (hG := hG))
    (N : HjNames) (P Q : Proto GF) (hs : List w8) (Z : Nat → IProp GF) :
    {{ hjPre N P Q hs Z }}
      (App (Val (N.w @!! go.GoType.PointerType net.http.response.ty @!! go!"Hijack")) (Val #()))
    {{ (bw : Loc), RET (PairV (PairV #(interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #N.t)
          #bw) #(interface.nil : GoInterface));
        connAt N.t N.cn true N.a N.la N.ra ∗ sendTok (Gg := hG.goose_globalGS) N.cn true Q [] ∗
        recvTok (Gg := hG.goose_globalGS) N.cn true P hs ∗ connFresh (Gg := hG.goose_globalGS) N.cn true ∗
        hjDone N hs }} := by
  wp_start as Hpre
  iunfold hjPre at Hpre
  icases Hpre with ⟨Hhd, Hec, Hwh, #Hconn, Hww, Hwraw, #Hmu, Hγh, #Hr, #Hrwc, #Hbr, #Hbw, Hbraw,
    #Hsrv, #Hs, Hst, #Hcr, #Htm, #Hcrwc, Hph, Hrr, #Hca, Hsend, Hfresh, #Hz, #Hpools, %b0, Hrdl⟩
  wp_auto
  ihave #Hs' := Hs
  iunfold srvConst at Hs'
  icases Hs' with ⟨#Htime, #Hsync, #Hatomic, -, -⟩
  wp_apply wp_with_defer as %defer defer
  wp_bind (App (Val #(methods _ _ _)) (Val #()))
  iapply (sync.atomic.Bool.wp_Load
    (structFieldRef net.http.response go!"handlerDone" N.w) (DFrac.own 1))
  · iexact Hatomic
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists false
  iframe Hhd
  iintro Hhd
  imod Hmask
  imodintro
  wp_auto
  wp_apply wp_disableWriteContinue $$ [$Hec] as Hec
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
  iunfold connMuInv at Hinv
  icases Hinv with ⟨%b, Hhj, Hγh2⟩
  ihave %Hag := ghostVar_agree N.γh _ _ _ _ $$ Hγh Hγh2
  subst Hag
  wp_apply wp_hijackLocked N.c N.cr N.s N.γ N.t N.cn N.a N.la N.ra P Q hs Z N.tm N.br N.bw 4096 b0
    $$ [$Hhj $Hr $Hrwc $Hbr $Hbw $Hbraw $Hsrv $Hs $Hst $Hcr $Htm $Hcrwc $Hph $Hrr $Hca $Hsend $Hz $Hrdl]
    as %buf ⟨Hhj, Hbraw, Hst, Hrecv, Hsend, Hleft, Hrdl⟩
  imod ghostVar_update_halves true N.γh _ _ $$ Hγh Hγh2 with ⟨Hγh, Hγh2⟩
  wp_apply wp_putBufioWriter wp_Reset N.ww 2048 (Or.inl rfl) $$ [$Hpools $Hwraw]
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hown Hhj Hγh2]
  · inext; iunfold connMuInv; iexists true; iframe Hhj Hγh2
  iapply HΦ
  iframe Hca Hsend Hrecv Hfresh
  iunfold hjDone
  iframe Hγh Hleft Hst Hhd Hrdl

theorem response.Hijack.wp_proof
    (wp_hijackLocked : conn.hijackLocked.spec (GF := GF) (hG := hG))
    (wp_Reset : EtcdGrove.bufio.Writer.Reset.spec (GF := GF) (hG := hG)) :
    response.Hijack.spec (GF := GF) (hG := hG) := by
  intro N P Q hs Z
  iintro Hpre
  iunfold hijackOk
  iintro %Φ HΦ
  iapply (wp_hijack wp_hijackLocked wp_Reset N P Q hs Z) $$ Hpre
  inext
  iintro %bw ⟨#Hca, Hsend, Hrecv, Hfresh, HD⟩
  iapply HΦ $$ Hca Hsend Hrecv Hfresh HD

end proof

end net.http
end Perennial

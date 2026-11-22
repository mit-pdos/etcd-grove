/-
The proof of `Client.send` (`Net/Spec/net/rpc/Client__send.lean`). Under `reqMutex` (`sendInv`) and
`mutex` (`muInv`): refused (shut down or closing), the call fails with `ErrShutdown` (`Call.done`),
ticket `none`; else it is numbered `n` (a time receipt for the number, `n + 1 < 2 ^ 64`), its names
allocated and recorded (`nm`), its entry put in `pending` (`callRes`), ticket `some n`. Then
`WriteRequest`: without a write error before, the encoding's continuation appends the request
(`req_append`); after a failed write the call, if still pending, fails with the write's error.
-/
module

public import Net.Spec.net.rpc.Client__send
public import Net.Spec.net.rpc.Call__done
public import Net.Spec.net.rpc.clientCodec__WriteRequest
public import Net.Proof.net.rpc.ClientGhost
public import Net.Proof.net.rpc.Errs
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Proof.ReceiptTactics

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
variable [π : NetProtoGS] [sync.Assumptions] [net.Assumptions]

theorem Client.send.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_WriteRequest : clientCodec.WriteRequest.spec (GF := GF) (hG := hG))
    (wp_done : Call.done.spec (GF := GF) (hG := hG)) :
    Client.send.spec (GF := GF) (hG := hG) := by
  intro c W a γ pc sm svc M S args reply ch γt γf K Φm Rargs D Θ C e0
  wp_start as ⟨#Hcl, %Hsv, #Hset, Henc, HD, #Hdec, Hγt, #Hf, Herr, Hdone⟩
  unfold isClientN clientAt
  icases Hcl with ⟨%cc, %t, %cn, %la, %ra, #Hcodec, #Hrwc, #Hconn, #Hci, #Hrpc, #Henv,
    #Hsmu, #Hmu⟩
  ihave #Henv' := Henv
  unfold cliEnv
  icases Henv' with ⟨%eof, %ueof, %ed, #Hio, #Hsync, #Heof, #Hueof, #Hed, #HefV, #HesV, #Hdbg⟩
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply +noauto wp_Lock _ _ $$ [$Hsync $Hsmu] as ⟨Hsown, Hsinv⟩
  wp_take_receipt as Hr1
  wp_auto
  iunfold sendInv at Hsinv
  icases Hsinv with ⟨%rq, %w0, %L, %Wd, %n1, Hreq, Hwerr, Hsend, Hreqs, Hsq1, ⟨%sd1, Hd1⟩,
    ⟨%HLok, %HLn, %HWd, %Hw0⟩⟩
  wp_apply wp_Lock _ _ $$ [$Hsync $Hmu] as ⟨Hown, Hinv⟩
  iunfold muInv at Hinv
  icases Hinv with ⟨%sq, %n, %mp, %m, %sd, %cls, %NM, Hseq, Hpend, Hmp, Hsd, Hcls, Hsq, Hr,
    ⟨%Hsqn, %Hbound⟩, Hdown, Hnm, %HNM, Hrest⟩
  ihave %Hsqa := ghostVar_agree $$ Hsq1 Hsq
  obtain ⟨-, rfl⟩ := Hsqa
  ihave #HesV' := HesV
  iunfold errors.newVar at HesV'
  icases HesV' with ⟨%xs, #Hxs, -⟩
  cases sd <;> cases cls
  rotate_left
  iterate 3 (
    -- refused: `ErrShutdown`
    wp_auto
    wp_apply wp_Unlock _ (muInv γ c) $$ [$Hsync $Hmu $Hown Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm
        Hrest]
    · iunfold muInv
      iexists sq, n1, mp, m, _, _, NM
      iframe Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm Hrest
      ipureintro; exact ⟨⟨Hsqn, Hbound⟩, HNM⟩
    imod ghost_map_insert_persist () (none : Option Nat) (by rfl) $$ Hγt with ⟨-, #Htk0⟩
    ihave #Htk : ticket γt none $$ []
    · iunfold ticket; iexact Htk0
    wp_apply wp_done pc sm args reply ch γ.conn γt γf K Φm Θ D none
        (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xs)
        $$ [$Hdbg $Hf $Htk $Hdone $Herr HD]
    · iunfold callPost
      iright; iright
      isplitr
      · ipureintro; exact ⟨by simp [interface.mkOk], notServerErr_errorString xs⟩
      isplitr
      · iapply errAny_newVar $$ HesV Hxs
      ileft; iexact HD
    wp_apply wp_Unlock _ (sendInv γ c cc cn W a) $$ [$Hsync $Hsmu $Hsown Hreq Hwerr Hsend Hreqs Hsq1
        Hd1]
    · iunfold sendInv
      iexists rq, w0, L, Wd, n1
      iframe Hreq Hwerr Hsend Hreqs Hsq1
      isplitl [Hd1]
      · iexists sd1; iexact Hd1
      ipureintro; exact ⟨HLok, HLn, HWd, Hw0⟩
    iapply HΦ
    iexists none
    iframe Htk
    iunfold sendRes
    iright
    iframe Henc
    unfold unsent
    itrivial)
  sorry

end proof

end net.rpc
end Perennial

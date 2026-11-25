/-
The proof of `Client.send.spec_closed` (`Net/Spec/net/rpc/Client__send.lean`): `Client.send`'s
refusal path (`Client__send.lean`). Under `mutex`, `closing` is `true`: `muInv`'s points-to of it
agrees with the persistent one of `cliClosed`; so the call fails with `ErrShutdown` (`Call.done`),
ticket `none`.
-/
module

public import Net.Spec.net.rpc.Client__send
public import Net.Spec.net.rpc.Call__done
public import Net.Proof.net.rpc.Errs
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

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
variable [package_sem' : net.rpc.Assumptions]
variable [π : NetProtoGS] [sync.Assumptions] [net.Assumptions]

theorem Client.send.wp_proof_closed (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_done : Call.done.spec (GF := GF) (hG := hG)) :
    Client.send.spec_closed (GF := GF) (hG := hG) := by
  intro c W a γ pc sm args reply ch γt γf K Φm D Θ
  wp_start as ⟨#Hcl, #Hclo, HD, Hγt, #Hf, Herr, Hdone⟩
  unfold isClientN clientAt
  icases Hcl with ⟨%cc, %t, %cn, %la, %ra, #Hcodec, #Hrwc, #Hconn, #Hci, #Hrpc, #Hsl, #Henv,
    #Hsmu, #Hmu⟩
  ihave #Henv' := Henv
  unfold cliEnv
  icases Henv' with ⟨%eof, %ueof, %ed, #Hio, #Hsync, #Heof, #Hueof, #Hed, #HefV, #HesV, #Hdbg⟩
  iunfold cliClosed at Hclo
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply wp_Lock _ _ $$ [$Hsync $Hsmu] as ⟨Hsown, Hsinv⟩
  wp_apply wp_Lock _ _ $$ [$Hsync $Hmu] as ⟨Hown, Hinv⟩
  iunfold muInv at Hinv
  icases Hinv with ⟨%sq, %n, %mp, %m, %sd, %cls, %NM, Hseq, Hpend, Hmp, Hsd, Hcls, Hsq, Hr,
    ⟨%Hsqn, %Hbound⟩, Hdown, Hnm, %HNM, Hrest⟩
  icombine Hcls Hclo gives %Hct
  subst Hct
  ihave #HesV' := HesV
  iunfold errors.newVar at HesV'
  icases HesV' with ⟨%xs, #Hxs, -⟩
  cases sd
  all_goals (
    -- refused: `ErrShutdown`
    wp_auto
    wp_apply wp_Unlock _ (muInv γ c) $$ [$Hsync $Hmu $Hown Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm
        Hrest]
    · iunfold muInv
      iexists sq, n, mp, m, _, _, NM
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
    wp_apply wp_Unlock _ (sendInv γ c cc cn W a) $$ [$Hsync $Hsmu $Hsown $Hsinv]
    iapply HΦ
    iexact Htk)

end proof

end net.rpc
end Perennial

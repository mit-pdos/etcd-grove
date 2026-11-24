/-
The proof of `Client.Close` (`Net/Spec/net/rpc/Client__Close.lean`): `closing` under `mutex`
(`muInv`), then the codec's `Close` with the library's `close_au`; `ErrShutdown` (`errAny_newVar`)
if it was set.
-/
module

public import Net.Spec.net.rpc.Client__Close
public import Net.Spec.net.rpc.clientCodec__Close
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
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [sync.Assumptions] [net.Assumptions]

theorem Client.Close.wp_proof (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_ccClose : clientCodec.Close.spec (GF := GF) (hG := hG)) :
    Client.Close.spec (GF := GF) (hG := hG) := by
  intro c W a
  wp_start as #Hc
  unfold isClient isClientN clientAt
  icases Hc with ⟨%γ, %cc, %t, %cn, %la, %ra, #Hcodec, #Hrwc, #Hconn, #Hci, #Hrpc, -, #Henv,
    #Hsmu, #Hmu⟩
  unfold cliEnv
  icases Henv with ⟨%eof, %ueof, %ed, #Hio, #Hsync, #Heof, #Hueof, #Hed, #HefV, #HesV, #Hdbg⟩
  wp_auto
  wp_apply wp_Lock _ _ $$ [$Hsync $Hmu] as ⟨Hown, Hinv⟩
  iunfold muInv at Hinv
  icases Hinv with ⟨%sq, %n, %mp, %m, %sd, %cls, %NM, Hseq, Hpend, Hmp, Hsd, Hcls, Hsq, Hr, %Hb,
    Hdown, Hnm, %Hnm, Hrest⟩
  wp_auto
  cases cls
  · -- not closing yet: set it, then close the connection
    wp_auto
    wp_apply wp_Unlock _ (muInv γ c) $$ [$Hsync $Hmu $Hown Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm
        Hrest]
    · iunfold muInv
      iexists sq, n, mp, m, sd, true, NM
      iframe Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm Hrest
      ipureintro; exact ⟨Hb, Hnm⟩
    wp_apply wp_ccClose cc t cn false a la ra (fun _ => iprop(True)) $$ [$Hrwc $Hconn] as
      %err ⟨%res, -, #Herr⟩
    · imod close_au (Gg := hG.goose_globalGS) cn false $$ Hci with ⟨%st, %d, Hst, Hd, Hk⟩
      imodintro
      iexists st, d
      iframe Hst Hd
      iintro %res %st' %d' %Hco Hst' Hd'
      imod Hk $$ %res %st' %d' %Hco Hst' Hd' with -
      imodintro
      itrivial
    iapply HΦ
    cases res with
    | none =>
      unfold net.resErr
      icases Herr with %Herr
      ileft; ipureintro; exact Herr
    | some k =>
      iright
      iapply errAny_resErr $$ Herr
  · -- closing already: `ErrShutdown`
    wp_auto
    wp_apply wp_Unlock _ (muInv γ c) $$ [$Hsync $Hmu $Hown Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm
        Hrest]
    · iunfold muInv
      iexists sq, n, mp, m, sd, true, NM
      iframe Hseq Hpend Hmp Hsd Hcls Hsq Hr Hdown Hnm Hrest
      ipureintro; exact ⟨Hb, Hnm⟩
    ihave #HesV' := HesV
    iunfold errors.newVar at HesV'
    icases HesV' with ⟨%x, #Hx, -⟩
    wp_auto
    iapply HΦ
    iright
    iapply errAny_newVar $$ HesV Hx

end proof

end net.rpc
end Perennial

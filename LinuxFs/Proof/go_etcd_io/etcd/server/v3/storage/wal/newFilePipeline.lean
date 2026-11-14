/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/newFilePipeline.lean`:
`chan.wp_make1` (`filec`, `donec`) and `wp_make2` (`errc`, capacity 1: `Buffered []`); the alive
flag (`dghostVar_alloc false`), `start_hsn` (`filec`), `start_spsc` (`errc`, its close predicate
`pipeErrR` with the flag's name), `alloc_broadcast_chan` (`donec`, `pipeClosedW`; its `.Unknown`
view kept for `isFilePipe`); the composite literal's points-to split by fields, all but `count`
made persistent; `Fork` of `run` with `pipeRun fp γ R dir dq j 0` (`run.wp_proof`).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__run

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions]

/-- A broadcast channel's owner keeps its state and gets the persistent `.Unknown` view. -/
theorem ownBroadcastChan_dup_unknown (ch : Loc) (γ : ChanNames) (Q : IProp GF) (st : Broadcast) :
    ownBroadcastChan ch γ Q st ⊢ ownBroadcastChan ch γ Q st ∗ ownBroadcastChan ch γ Q .Unknown := by
  iintro H
  icases ownBroadcastChan_open _ _ _ _ $$ H with ⟨%γch, #Hint, Hst⟩
  isplitl [Hst]
  · iapply ownBroadcastChan_close ch γ Q st γch $$ [$Hint $Hst]
  · iapply ownBroadcastChan_close ch γ Q .Unknown γch $$ [$Hint]

theorem go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline.wp_proof
    (wp_run : go_etcd_io.etcd.server.v3.storage.wal.filePipeline.run.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline.spec (GF := GF) (hG := hG) := by
  intro lg dir sz R dq j hsz0 hsz1 hdir hsz8
  wp_start as ⟨#Hlg, #Hos, #Hsi, #Hpkg, Hres, Hc⟩
  ihave %hlg := zapLoggerOk_ne_null lg $$ Hlg
  (try wp_auto)
  rw [decide_eq_false hlg]
  (try wp_auto)
  wp_apply (chan.wp_make1 (V := Loc)) as %fc %γfc ⟨#Hfc, -, Hofc⟩
  (try wp_auto)
  wp_apply (chan.wp_make2 (V := GoInterface) (W64 1)) as %ec %γec ⟨#Hec, -, Hoec⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply (chan.wp_make1 (V := Unit)) as %dc %γdc ⟨#Hdc, -, Hodc⟩
  (try wp_auto)
  imod (dghostVar_alloc (GF := GF) false) with ⟨%γa, Halive⟩
  imod start_hsn fc (fun n lf => pipeFile (GF := GF) j dir n lf) (pipeQ j) γfc $$ Hfc Hofc
    with ⟨%γf, %hγf, #Hhsn, Hsnd, Hrcv⟩
  imod start_spsc ec (pipeErrP (GF := GF) R dir dq j)
    (fun sent => iprop(⌜sent ≠ []⌝ ∨ pipeLeft (GF := GF) R dir dq j ∗
      dghostVar γa DFrac.discard true)) γec $$ Hec [Hoec] with ⟨%γe, #Hspsc, Hprod, Hcons⟩
  · iright; iexact Hoec
  imod alloc_broadcast_chan (dghostVar (GF := GF) γa DFrac.discard true) γdc dc $$ Hdc Hodc
    with Hbc
  icases ownBroadcastChan_dup_unknown dc γdc _ _ $$ Hbc with ⟨Hbc, #Hbcu⟩
  let γ : PipeNames := ⟨fc, ec, dc, γf, γe, γdc, γa⟩
  iStructNamed «$r0»
  ipersist lg
  ipersist dir
  ipersist size
  ipersist filec
  ipersist errc
  ipersist donec
  ihave #Hfp : isFilePipe «$r0_ptr» γ R dir dq j sz $$ []
  · iunfold isFilePipe
    iexists lg
    iframe #
    isplitl []
    · iapply (show isSpsc γe ec (pipeErrP (GF := GF) R dir dq j)
          (fun sent => iprop(⌜sent ≠ []⌝ ∨ pipeLeft (GF := GF) R dir dq j ∗
            dghostVar γa DFrac.discard true)) ⊢
          isSpsc γ.e γ.ec (pipeErrP R dir dq j) (pipeErrR γ R dir dq j) from .rfl) $$ Hspsc
    isplitl []
    · iapply (show ownBroadcastChan dc γdc (dghostVar (GF := GF) γa DFrac.discard true) .Unknown ⊢
          ownBroadcastChan γ.dc γ.d (pipeClosedW γ) .Unknown from .rfl) $$ Hbcu
    ipureintro; exact ⟨hsz0, hsz1, hdir, hsz8⟩
  wp_apply wp_fork $$ [Hsnd Hprod count Hres Hc]
  · wp_apply wp_run «$r0_ptr» γ R dir dq j sz $$ [Hsnd Hprod count Hres Hc]
    · iframe Hfp
      iunfold pipeRun
      iframe
      ipureintro; decide
    ipureintro; exact isPanic_intoVal _
  (try wp_auto)
  iapply HΦ
  iexists γ
  iframe Hfp
  iunfold pipeMain
  iframe

end proof

end EtcdGrove
end Perennial

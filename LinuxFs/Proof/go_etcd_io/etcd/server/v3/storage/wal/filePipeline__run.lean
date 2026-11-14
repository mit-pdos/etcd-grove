/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/filePipeline__run.lean`
(`wp_with_defer`, `wp_for` with `∃ n, pipeRun fp γ R dir dq j n`):
* `alloc` fails: the error sent on `errc` (`wp_spsc_send`, `pipeErrP`: `pipeLeft`, the claim on
  `pipeTmp n`), return; the deferred `close(errc)` with `pipeErrR [e]` (its left disjunct);
* the file: the `select` (`chan.wp_select_blocking`): the send on `filec` (`hsn_send_au`, `hsnSnd n`,
  `pipeFile n`) gives `hsnSnd (n + 1)` and `pipeQ j n`: `pipeRun (n + 1)`; `donec`'s receive
  (`broadcast_chan_receive`) gives `pipeClosedW`: `os.Remove(f.Name())` (`wp_removeTmp`, the
  trivial update; the claim back as a `tmpClaim`), the promoted `(*os.File).Close`, return; the
  deferred close with `pipeErrR []` (`pipeLeft` and `pipeClosedW`).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__run
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__alloc
public import LinuxFs.Spec.os.Remove
public import LinuxFs.Spec.os.File__Name
public import LinuxFs.Spec.os.File__Close
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PipeLemmas

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
variable [fu_sem : go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.filePipeline.run.wp_proof
    (wp_alloc : go_etcd_io.etcd.server.v3.storage.wal.filePipeline.alloc.spec (GF := GF) (hG := hG))
    (wp_Remove : os.Remove.specFileSnc (GF := GF) (hG := hG))
    (wp_Name : os.File.Name.spec (GF := GF) (hG := hG))
    (wp_Close : os.File.Close.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.filePipeline.run.spec (GF := GF) (hG := hG) := by
  intro fp γ R dir dq j sz
  wp_start as ⟨#Hfp, Hrun⟩
  ihave #Hfp' : isFilePipe fp γ R dir dq j sz $$ [Hfp]
  · iexact Hfp
  iunfold isFilePipe at Hfp
  icases Hfp with ⟨%lg, #Hlg, #Hdir, #Hsz, #Hfc, #Hec, #Hdc, #Hhsn, #Hspsc, #Hbc, #Hlgok, #Hos,
    #Hsi, #Hpkg, %hsz⟩
  (try wp_auto)
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  ihave HI : (∃ n, pipeRun fp γ R dir dq j n) $$ [Hrun]
  · iexists 0; iexact Hrun
  wp_for HI
  icases HI with ⟨Hsnd, Hprod, Hcnt, Hc, Hres, %hn⟩
  wp_apply wp_alloc fp γ R dir dq j sz n hn $$ [$Hfp' $Hcnt $Hc $Hres] as %lf %err ⟨Hres, Hr⟩
  icases Hr with (⟨%he, Hcnt, Hfile⟩ | ⟨%he, Hcnt, Hc⟩)
  · subst he
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the file sent on `filec`
      simp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, γ.fc, γ.f.ch, lf
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply isHsn_is_chan $$ Hhsn
      iapply hsn_send_au γ.f γ.fc lf (fun n lf => pipeFile j dir n lf) (pipeQ j) n _ $$
        [$Hlc1 $Hlc2 $Hlc3] Hhsn Hsnd Hfile
      inext
      iintro Hsnd HQ
      (try wp_auto)
      wp_for_post
      iunfold pipeQ at HQ
      icases HQ with ⟨Hc, %hn1⟩
      iframe
      iexists n + 1
      iunfold pipeRun
      iframe
      ipureintro; exact hn1
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `donec` closed
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, γ.dc, γ.d
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply ownBroadcastChan_is_chan _ _ _ _ $$ Hbc
      iapply broadcast_chan_receive γ.dc γ.d (pipeClosedW γ) _ .Unknown $$ Hbc
      iintro ⟨#Hcl, -⟩
      (try wp_auto)
      iunfold pipeFile at Hfile
      icases Hfile with ⟨%f, %fd, %i, %m, %h, #Hlf, Hf, Hoff, Hfd, Hm, Hz, Hn, %hpf⟩
      obtain ⟨hfd, hmaps, hcur, hcut, hlo, -, -, hzp⟩ := hpf
      iunfold fileutil.lockedFile at Hlf
      iStructNamed Hlf
      wp_method_call
      wp_call
      (try wp_auto)
      wp_apply wp_Name f fd _ _ $$ [$Hf] as Hf
      (try wp_auto)
      iunfold pipeRes at Hres
      icases Hres with ⟨Hperm, Hp⟩
      ihave Ht := zerosA_trFile i m hmaps hcut hlo (OsMeta.ZeroPg.zfGe hzp) $$ [$Hm $Hz]
      wp_apply wp_removeTmp wp_Remove R dir dq j (pipeTmp n) i h _ (pipeTmp_nameOk n) hcur
        $$ [$Hos $Hsi $Hp $Hperm $Hn $Ht] as %re ⟨Hp, Hperm, Hc⟩
      (try wp_auto)
      wp_method_call
      wp_call
      (try wp_auto)
      wp_apply wp_Close f fd _ _ $$ [$Hos $Hf $Hfd] as %ce -
      (try wp_auto)
      wp_for_post
      wp_apply wp_spsc_close γ.e γ.ec (pipeErrP R dir dq j) (pipeErrR γ R dir dq j)
        ([] : List GoInterface) $$ [$Hspsc $Hprod Hp Hperm Hc]
      · iunfold pipeErrR
        iright
        iframe Hcl
        iunfold pipeLeft
        iunfold pipeRes
        iframe Hperm Hp
        iexists pipeTmp n
        iframe Hc
        ipureintro; exact pipeTmp_mem n
      (try wp_auto)
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · cases err with
    | nil => exact absurd rfl he
    | ok ei =>
    (try wp_auto)
    wp_apply wp_spsc_send γ.e γ.ec (pipeErrP R dir dq j) (pipeErrR γ R dir dq j) []
      (GoInterface.ok ei) $$ [$Hspsc $Hprod Hres Hc]
    · iunfold pipeErrP
      isplitr
      · ipureintro; exact he
      iunfold pipeLeft
      iframe Hres
      iexists pipeTmp n
      iframe Hc
      ipureintro; exact pipeTmp_mem n
    iintro Hprod
    (try wp_auto)
    wp_for_post
    wp_apply wp_spsc_close γ.e γ.ec (pipeErrP R dir dq j) (pipeErrR γ R dir dq j)
      ([] ++ [GoInterface.ok ei]) $$ [$Hspsc $Hprod]
    · iunfold pipeErrR; ileft; ipureintro; simp
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial

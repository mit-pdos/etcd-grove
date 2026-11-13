/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/filePipeline__Open.lean`: the
`select` over `filec` (the indexed handshake's receive) and `errc` (the SPSC receive; closed and
empty excluded by the alive flag).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__Open

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

/-- The alive flag excludes `Close`'s witness. -/
theorem pipe_alive_closed (γ : PipeNames) :
    dghostVar (GF := GF) γ.a (DFrac.own 1) false ∗ pipeClosedW γ ⊢ False := by
  unfold pipeClosedW
  iintro ⟨H1, H2⟩
  ihave %h := dghostVar_agree _ _ _ _ _ $$ H1 H2
  cases h

theorem go_etcd_io.etcd.server.v3.storage.wal.filePipeline.Open.wp_proof :
    go_etcd_io.etcd.server.v3.storage.wal.filePipeline.Open.spec (GF := GF) (hG := hG) := by
  intro fp γ R dir dq j sz n
  wp_start as ⟨#Hfp, Hmain, HQ⟩
  iunfold isFilePipe at Hfp
  icases Hfp with ⟨%lg, #Hlg, #Hdir, #Hsz, #Hfc, #Hec, #Hdc, #Hhsn, #Hspsc, #Hbc, #Hrest⟩
  iunfold pipeMain at Hmain
  icases Hmain with ⟨Hrcv, Hcons, Hpend, Halive⟩
  wp_auto_lc 2
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- a file from `filec`
    simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, γ.fc, γ.f.ch
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply isHsn_is_chan $$ Hhsn
    iapply hsn_receive_au γ.f γ.fc (fun n lf => pipeFile j dir n lf) (pipeQ j) n $$
      [$Hlc1 $Hlc2] Hhsn Hrcv HQ
    inext
    iintro %lf Hrcv Hfile
    wp_auto
    iapply HΦ
    ileft
    iunfold pipeMain
    iframe
    ipureintro; rfl
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- an error from `errc`
    simp only [chan.blockingClausePre]
    iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, γ.ec,
      γ.e.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · iunfold isSpsc at Hspsc; icases Hspsc with ⟨$, -⟩
    iapply spsc_rcv_au γ.e γ.ec (pipeErrP R dir dq j) (pipeErrR γ R dir dq j) [] $$
      Hspsc [$Hlc1 $Hlc2] Hcons
    inext
    iintro %e %ok Hok
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      iunfold pipeErrR at Hok
      icases Hok with ⟨(%Hne | ⟨-, #Hcl⟩), -⟩
      · exact absurd rfl Hne
      · iexfalso
        iapply pipe_alive_closed γ $$ [$Halive $Hcl]
    · simp only [↓reduceIte, List.length_nil, List.nil_append]
      icases Hok with ⟨HP, Hcons⟩
      iunfold pipeErrP at HP
      icases HP with ⟨%Hne, Hleft⟩
      wp_auto
      iapply HΦ
      iright
      iunfold pipeDead
      iframe
      ipureintro; exact ⟨Hne, rfl⟩
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial

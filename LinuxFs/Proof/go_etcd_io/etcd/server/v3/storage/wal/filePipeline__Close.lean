/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/filePipeline__Close.lean`: the
alive flag becomes `Close`'s witness (`pipeClosedW`), `donec`'s close carries it, and `errc`'s
receive gives the resources (its value's, or its close's).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.filePipeline__Close

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

/-- `Close`'s witness from the alive flag. -/
theorem pipe_close_witness (γ : PipeNames) :
    ⊢ dghostVar (GF := GF) γ.a (DFrac.own 1) false ==∗ pipeClosedW γ := by
  iintro H
  imod dghostVar_update true γ.a false $$ H with H
  unfold pipeClosedW
  iapply dghostVar_persist γ.a 1 true $$ H

theorem go_etcd_io.etcd.server.v3.storage.wal.filePipeline.Close.wp_proof :
    go_etcd_io.etcd.server.v3.storage.wal.filePipeline.Close.spec (GF := GF) (hG := hG) := by
  intro fp γ R dir dq j sz
  wp_start as ⟨#Hfp, Hst⟩
  iunfold isFilePipe at Hfp
  icases Hfp with ⟨%lg, #Hlg, #Hdir, #Hsz, #Hfc, #Hec, #Hdc, #Hhsn, #Hspsc, #Hbc, #Hrest⟩
  icases Hst with (⟨%n, Hmain⟩ | ⟨%e, Hdead, Hleft⟩)
  · iunfold pipeMain at Hmain
    icases Hmain with ⟨-, Hcons, Hpend, Halive⟩
    imod pipe_close_witness γ $$ Halive with #Hcl
    wp_auto
    wp_apply wp_broadcast_chan_close γ.dc γ.d (pipeClosedW γ) $$ [$Hpend $Hcl] as -
    wp_apply wp_spsc_receive γ.e γ.ec (pipeErrP R dir dq j) (pipeErrR γ R dir dq j) [] $$
      [$Hspsc $Hcons] as %v %ok Hok
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      iunfold pipeErrR at Hok
      icases Hok with ⟨(%Hne | ⟨Hleft, -⟩), -⟩
      · exact absurd rfl Hne
      · iapply HΦ $$ Hleft
    · simp only [↓reduceIte]
      icases Hok with ⟨HP, -⟩
      iunfold pipeErrP at HP
      icases HP with ⟨-, Hleft⟩
      iapply HΦ $$ Hleft
  · iunfold pipeDead at Hdead
    icases Hdead with ⟨Hcons, Hpend, Halive⟩
    imod pipe_close_witness γ $$ Halive with #Hcl
    wp_auto
    wp_apply wp_broadcast_chan_close γ.dc γ.d (pipeClosedW γ) $$ [$Hpend $Hcl] as -
    wp_apply wp_spsc_receive γ.e γ.ec (pipeErrP R dir dq j) (pipeErrR γ R dir dq j) [e] $$
      [$Hspsc $Hcons] as %v %ok -
    iapply HΦ $$ Hleft

end proof

end EtcdGrove
end Perennial

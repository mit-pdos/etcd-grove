/-
(hraft_robust R3) The proof of `disk.(*Disk).LastIndex`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__LastIndex
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__lastIndex
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.InvLemmas
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.LastIndex.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_lastIndex : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.lastIndex.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.LastIndex.spec (GF := GF) (hG := hG) := by
  intro g d Wl Ws Wf
  iintro %Φ #Hdisk HAU
  iunfold isDisk at Hdisk
  icases Hdisk with ⟨%mu, #Hpkg, #Hmu, #Hisl, #Hfile, #Hinv, #Hdinv, #Hos, #Hsh, %Hf⟩
  wp_method_call
  wp_call
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply (lc := 2) wp_Lock $$ [$Hisl] as ⟨Hlocked, HR⟩
  iunfold diskLockInv at HR
  icases HR with ⟨%I, %stg, %qc, Hmem, Hrec, %HIok, Hdh, Hcp⟩
  try wp_auto
  wp_apply wp_lastIndex $$ [$Hmem] as Hmem
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  imod (diskReadL g Wl Ws Wf I stg (fun A => Φ (PairV #A.hi #interface.nil))) $$ Hinv Hrec Hlc1 Hlc2 HAU Hnc
    with ⟨Hnc, Hrec, HΦ⟩
  imodintro
  iframe Hnc
  try wp_auto
  wp_apply wp_Unlock $$ [$Hisl $Hlocked Hmem Hrec Hdh Hcp]
  · inext; iunfold diskLockInv; iexists I, stg, qc; iframe; ipureintro; exact HIok
  try wp_auto
  rw [show (I.absL stg).hi = I.hi from rfl]
  iexact HΦ

end sec

end Perennial

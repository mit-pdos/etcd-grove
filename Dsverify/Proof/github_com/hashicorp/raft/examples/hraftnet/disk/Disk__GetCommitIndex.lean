/-
(hraft_robust R3) The proof of `disk.(*Disk).GetCommitIndex`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Disk__GetCommitIndex
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
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

set_option goose.wp.extras true

theorem dk_readCi_gt (I : DiskImg) (stg : w64) (h : uint.Z I.hi < uint.Z I.commit) :
    (I.absL stg).readCi = I.hi := by
  unfold LogAbs.readCi DiskImg.absL; simp only; rw [if_pos (by word)]

theorem dk_readCi_le (I : DiskImg) (stg : w64) (h : ¬ uint.Z I.hi < uint.Z I.commit) :
    (I.absL stg).readCi = I.commit := by
  unfold LogAbs.readCi DiskImg.absL; simp only; rw [if_neg (by word)]

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Disk.GetCommitIndex.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_lastIndex : github_com.hashicorp.raft.examples.hraftnet.disk.Disk.lastIndex.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Disk.GetCommitIndex.spec (GF := GF) (hG := hG) := by
  intro g d Wl Ws Wf
  iintro %Φ #Hdisk HAU
  iunfold isDisk at Hdisk
  icases Hdisk with ⟨%mu, #Hpkg, #Hmu, #Hisl, #Hfile, #Hinv, #Hdinv, #Hos, #Hsh, %Hf⟩
  wp_method_call
  wp_call
  try wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply (lc := 2) wp_Lock $$ [$Hisl] as ⟨Hlocked, HR⟩
  iunfold diskLockInv at HR
  icases HR with ⟨%I, %stg, %qc, Hmem, Hrec, %HIok, Hdh, Hcp⟩
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  imod (diskReadL g Wl Ws Wf I stg (fun A => Φ (PairV #A.readCi #interface.nil))) $$ Hinv Hrec Hlc1 Hlc2 HAU Hnc
    with ⟨Hnc, Hrec, HΦ⟩
  imodintro
  iframe Hnc
  try wp_auto
  wp_apply wp_lastIndex $$ [$Hmem] as Hmem
  iunfold diskMem at Hmem
  icases Hmem with ⟨%es, %ks, %vs, %iks, %ivs, %lvs, %kss, %vss, %ikss, Hents, Hes, Hescap, #Hent,
    Hkeys, Hks, Hkscap, #Hkr, Hvals, Hvs, Hvscap, #Hvr, Hikeys, Hiks, Hikscap, #Hikr,
    Hivals, Hivs, Hivscap, Hstaged, Hcommit⟩
  try wp_auto
  wp_if_destruct
  · try wp_auto
    wp_apply wp_Unlock $$ [$Hisl $Hlocked Hrec Hdh Hcp Hents Hes Hescap Hkeys Hks Hkscap Hvals Hvs Hvscap
      Hikeys Hiks Hikscap Hivals Hivs Hivscap Hstaged Hcommit]
    · inext; iunfold diskLockInv; iexists I, stg, qc; iframe
      isplitl
      · iunfold diskMem; iexists es, ks, vs, iks, ivs, lvs, kss, vss, ikss; iframe; iframe #
      ipureintro; exact HIok
    try wp_auto
    rw [dk_readCi_gt I stg Hif]
    iexact HΦ
  · try wp_auto
    wp_apply wp_Unlock $$ [$Hisl $Hlocked Hrec Hdh Hcp Hents Hes Hescap Hkeys Hks Hkscap Hvals Hvs Hvscap
      Hikeys Hiks Hikscap Hivals Hivs Hivscap Hstaged Hcommit]
    · inext; iunfold diskLockInv; iexists I, stg, qc; iframe
      isplitl
      · iunfold diskMem; iexists es, ks, vs, iks, ivs, lvs, kss, vss, ikss; iframe; iframe #
      ipureintro; exact HIok
    try wp_auto
    rw [dk_readCi_le I stg Hif]
    iexact HΦ

end sec

end Perennial

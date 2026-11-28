/-
(hraft_robust R3) The proof of `disk.(*Snaps).Create` (`snap.go`), as `examples/snapstore`'s.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.disk.Snaps__Create
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock
public import Perennial.Spec.strconv.Itoa

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.Create.wp_proof
    (wp_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG))
    (wp_Itoa : strconv.Itoa.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.Create.spec (GF := GF) (hG := hG) :=
  fun g s Qc Wf ver idx term cfgIdx cfg trans => by
  wp_start as #Hsn
  ihave #Hsn2 := Hsn
  iunfold isSnaps at Hsn2
  icases Hsn2 with ⟨%mu, #Hpkg, #Hmu, #Hisl, #Hfile, #Hinv, #Hdinv, #Hos, #Hsh, %Hf⟩
  wp_auto
  wp_apply wp_Lock $$ [$Hisl] as ⟨Hlocked, HR⟩
  iunfold snapsLockInv at HR
  icases HR with ⟨%lat, %lt, %nid, %has, %mv, %dt, %qc, Hmem, %Hmv, #Hr, Hrec, Hdh, Hcp⟩
  iunfold snapsMemAt at Hmem
  icases Hmem with ⟨Hhas, Hmeta, Hdata, Hnid, Hm⟩
  wp_auto
  wp_apply wp_Itoa
  wp_apply wp_Itoa
  wp_apply wp_Itoa
  wp_apply wp_Unlock $$ [$Hisl $Hlocked Hhas Hmeta Hdata Hnid Hm Hrec Hdh Hcp]
  · inext; iunfold snapsLockInv; iexists lat, lt, _, has, mv, dt, qc
    iunfold snapsMemAt; iframe; iframe #; ipureintro; exact Hmv
  wp_alloc k as Hk
  iStructNamed Hk
  ihave %Hmnn := typedPointsto_not_null _ _ _ $$ «meta'»
  iStructNamed «meta'»
  ipersist st
  ipersist Version
  ipersist ID
  ipersist Index
  ipersist Term
  ipersist Peers
  ipersist Configuration
  ipersist ConfigurationIndex
  wp_auto
  iapply HΦ
  unfold sinkCore sinkSt
  iframe #
  isplitr
  · ipureintro; exact Hmnn
  iexists slice.nil
  iframe
  isplitl
  · iapply ownSlice_nil
  iapply ownSliceCap_nil

end proof

end Perennial

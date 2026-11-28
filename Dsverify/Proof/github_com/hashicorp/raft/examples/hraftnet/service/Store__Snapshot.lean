/-
The proof of `service.Store.Snapshot` (adapted from dsverify-lab's hr3 `store__Snapshot.lean`, 241f27e).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.Store__Snapshot
public import Perennial.Spec.sync.Mutex__Lock
public import Perennial.Spec.sync.Mutex__Unlock

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.service github_com.hashicorp.raft
  github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

theorem github_com.hashicorp.raft.examples.hraftnet.service.Store.Snapshot.wp_proof
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.service.Store.Snapshot.spec (GF := GF) (hG := hG) := by
  intro γ fc alb i s k0 x
  wp_start as ⟨#Hst, Hown, %Hk0, #Hnc⟩
  unfold isStore
  icases Hst with ⟨#Hlock, #Hfr, #Hls, #Hdb, #Hsv⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply wp_Mutex_Lock $$ [$Hlock] as ⟨Hlocked, Hinv⟩
  unfold storeInv fsmOwn
  icases Hinv with ⟨%es, #Hpre, #Hflb, Halb2, Hpres, Hval, Hidx, %Hes⟩
  ihave %Hag := monoNatAuthOwn_agree _ _ _ _ _ $$ Hown Halb2
  have Hk0e : es.length = k0 := Hag.2.symm
  subst Hk0e
  wp_auto
  wp_alloc sn as Hsn
  ipersist Hsn
  wp_auto
  wp_apply wp_Mutex_Unlock $$ [$Hlock $Hlocked Halb2 Hpres Hval Hidx]
  · inext; iexists es; iframe; iframe #; ipureintro; exact Hes
  try wp_auto
  iapply HΦ
  iframe
  unfold snapVal snapP
  iexists es
  iframe #
  ipureintro; exact ⟨⟨Hk0, rfl, Hes.1, Hes.2⟩, Hes.1⟩

end proof

end Perennial

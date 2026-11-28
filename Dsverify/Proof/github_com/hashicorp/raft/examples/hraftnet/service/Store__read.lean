/-
The proof of `service.Store.read` (S6).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.Store__read
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

theorem github_com.hashicorp.raft.examples.hraftnet.service.Store.read.wp_proof
    (wp_Mutex_Lock : sync.Mutex.Lock.spec (GF := GF) (hG := hG))
    (wp_Mutex_Unlock : sync.Mutex.Unlock.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.examples.hraftnet.service.Store.read.spec (GF := GF) (hG := hG) := by
  intro γ fc alb i s k0
  wp_start as ⟨#Hst, #Hk0⟩
  unfold isStore
  icases Hst with ⟨#Hlock, #Hfr, #Hls, #Hdb, #Hsv⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply wp_Mutex_Lock $$ [$Hlock] as ⟨Hlocked, Hinv⟩
  unfold storeInv
  icases Hinv with ⟨%es, #Hpre, #Hflb, Halb2, Hpres, Hval, Hidx, %Hes⟩
  ihave %Hle : ⌜k0 ≤ es.length⌝ $$ [Halb2]
  · icases Hk0 with (%h0 | #Hlb)
    · ipureintro; omega
    · unfold appliedLb
      ihave %h := monoNatLbOwn_valid _ _ _ _ $$ Halb2 Hlb
      ipureintro; exact h.2
  wp_auto
  wp_apply wp_Mutex_Unlock $$ [$Hlock $Hlocked Halb2 Hpres Hval Hidx]
  · inext; iexists es; iframe; iframe #; ipureintro; exact Hes
  try wp_auto
  iapply HΦ
  iexists es
  iframe #
  ipureintro; exact ⟨Hes.2, Hle, rfl⟩

end proof

end Perennial

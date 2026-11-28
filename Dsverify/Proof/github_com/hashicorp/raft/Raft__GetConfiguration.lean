/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__GetConfiguration.lean (241f27e).
-/
/-
The proof of `raft.Raft.GetConfiguration` (stage 4 interface: a new spec, to be proved).
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__GetConfiguration
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getLatestConfiguration
public import Dsverify.Proof.github_com.hashicorp.raft.FutBase

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

theorem github_com.hashicorp.raft.Raft.GetConfiguration.wp_proof
    (wp_getLatestConfiguration :
      github_com.hashicorp.raft.Raft.getLatestConfiguration.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.GetConfiguration.spec (GF := GF) (hG := hG) := by
  intro r γ rc i
  wp_start as #Hr
  wp_auto
  irename «$r0» => Hf
  generalize «$r0_ptr» = f at *
  iStructNamed Hf
  try simp only [zeroValDef] at *
  iStructNamed deferError
  wp_apply (lc := 2) futProof.wp_cf_init f (fun _ => iprop(True)) null $$ [$errCh]
    as ⟨%ch, %γe, %Hne, HerrCh, #Hspsc, Hprod, Hcons⟩
  wp_apply wp_getLatestConfiguration $$ [$Hr] as %c #Hc
  ipersist HerrCh
  ipersist ShutdownCh
  wp_apply futProof.wp_cf_respond f (fun _ => iprop(True)) interface.nil $$ [responded Hprod] as -
  · ileft
    isplitl
    · unfold deferResp
      iexists ch
      iframe #
      iright
      iframe
      ipureintro; exact Hne
    · itrivial
  iapply HΦ
  iexists f, _
  iframe
  isplitr
  · ipureintro; rfl
  isplitr
  · iexact Hc
  unfold deferWait
  iexists ch, γe
  iframe
  iframe #
  isplitr
  · ipureintro; exact Hne
  ileft; ipureintro; rfl
  done

end proof

end Perennial

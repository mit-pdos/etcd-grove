/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/randomTimeout.lean (241f27e).
-/
/-
The proof of `raft.randomTimeout`: `nil` for a zero duration, otherwise `time.After`'s channel.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.randomTimeout
public import Perennial.Proof.time.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link

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

open github_com.hashicorp.raft

theorem github_com.hashicorp.raft.randomTimeout.wp_proof :
    github_com.hashicorp.raft.randomTimeout.spec (GF := GF) (hG := hG) :=
  fun d => by
  wp_start as -
  wp_auto
  wp_if_destruct
  · iapply HΦ
    ileft; ipureintro; rfl
  · wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %x -
    have hd : uint.Z d ≠ 0 := fun h => Hif (by word)
    simp only [hd, ↓reduceIte]
    wp_auto
    wp_apply time.After.spec_pkgInit time.wp_After _ as %ch %γc #Hbag
    iapply HΦ
    iright; iexists γc; iexact Hbag

end proof

end Perennial

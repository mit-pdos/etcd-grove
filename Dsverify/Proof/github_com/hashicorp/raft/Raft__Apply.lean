/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__Apply.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).Apply`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__Apply
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__ApplyLog

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

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.Raft.Apply.wp_proof
    (wp_ApplyLog : github_com.hashicorp.raft.Raft.ApplyLog.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.Apply.spec (GF := GF) (hG := hG) := by
  intro r γ rc i cmd d n tmo
  wp_start as ⟨#Hr, #Hd, Htok⟩
  wp_auto
  wp_apply wp_ApplyLog $$ [$Hr $Htok] as %fi Hfi
  · isplitr; · iexact Hd
    iexists []; iapply ownSlice_nil
  iapply HΦ $$ Hfi

end proof

end Perennial

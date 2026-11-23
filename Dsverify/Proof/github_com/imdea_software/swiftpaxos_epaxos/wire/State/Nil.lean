module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.State

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions]
  [TH : TreemapHyp GF]

theorem state.NIL.spec_holds : state.NIL.spec (GF := GF) := by
  unfold state.NIL.spec
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := w8) (t := go.byte) []
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  wp_end

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos

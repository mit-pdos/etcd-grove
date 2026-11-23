module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.State.Nil

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

theorem state.NOOP.spec_holds : state.NOOP.spec (GF := GF) := by
  unfold state.NOOP.spec
  have hnil := state.NIL.spec_holds (GF := GF)
  unfold state.NIL.spec at hnil
  wp_start
  wp_auto
  wp_apply hnil as %v Hv
  ipersist Hv
  wp_apply wp_slice_literal (V := state.Command) [state.Command.mk (W8 0) (W64 0) v]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  wp_end
  unfold ownCmds
  iexists _
  iframe
  isplitr
  · ipureintro; rfl
  iapply BigSepL.bigSepL_singleton.2
  iexists _
  isplitr
  · ipureintro; rfl
  unfold cmdOk
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iexact Hv

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos

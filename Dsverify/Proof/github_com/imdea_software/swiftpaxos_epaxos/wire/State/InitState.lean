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

theorem state.InitState.spec_holds : state.InitState.spec (GF := GF) := by
  unfold state.InitState.spec
  wp_start
  wp_auto
  imod sync.init_Mutex iprop(True) ⊤ «$v0_ptr» $$ «$v0» [] with #Hmu
  · inext; itrivial
  wp_apply +noauto TH.NewWith_spec as %store Hstore
  · iexact Hpkg
  wp_pures
  wp_alloc st as Hst
  ipersist Hst
  wp_auto
  iapply HΦ
  rw [isState_unseal]
  unfold isStateDef
  iexists «$v0_ptr», store, ∅
  iframe
  isplitr
  · iexact Hst
  isplitr
  · iexact Hmu
  isplitr
  · ipureintro; intro k; rfl
  · iapply BigSepM.bigSepM_empty_intro (P := iprop(True)); itrivial

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos

/-
`coordinator.New(tport)`: the coordinator with no replica, its lock invariant allocated.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [log.Assumptions] [LogHyp GF] [examples.craqnet.Assumptions] [store.Assumptions] [store.kv.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions] [node.Assumptions] [coordinator.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]

theorem coordinator.wp_New : coordinator.wp_New.spec (GF := GF) (hG := hG) := by
  intro cfg f
  wp_start as ⟨%Hchain, #Hctx, #Hfac, Hres⟩
  iapply wp_fupd
  wp_auto
  iStructNamed «$r0»
  unfold coordRes
  icases Hres with ⟨Htok, Hnext, Hroles⟩
  imod sync.init_Mutex (coordLock cfg «$r0_ptr») ⊤ _ $$ mu [replicas version head tail Htok Hnext Hroles] with #Hmu
  · inext
    unfold coordLock
    iexists slice.nil, [], 0, null, null
    iframe replicas head tail version
    isplitl []
    · simp only [List.map_nil]; iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl [Hnext]
    · iExactEq Hnext; rfl
    isplitr
    · ipureintro; simp [repsWf]
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    simp only [↓reduceIte]
    iframe Htok
    iapply BigSepL.bigSepL_mono _ $$ Hroles
    intro _ a _
    unfold joinRes
    iintro H; iright; iframe H; ipureintro; simp
  ipersist tport
  imodintro
  iapply HΦ
  unfold isCoord coordDef
  iframe #
  ipureintro
  exact Hchain

end proof

end github_com.despreston.go_craq

end Perennial

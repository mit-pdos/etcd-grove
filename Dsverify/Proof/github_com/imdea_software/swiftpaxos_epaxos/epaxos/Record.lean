/-
`(*Replica).recordInstanceMetadata`, `(*Replica).recordCommands`: nothing without a durable log
(`Durable` is false).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.EpBase

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

theorem wp_recordInstanceMetadata (r rr inst : Loc) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fld rr go!"Durable" ↦□ false }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"recordInstanceMetadata"))
        (Val #inst))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hrr, #Hd⟩
  wp_auto
  wp_end

theorem wp_recordCommands (r rr : Loc) (cs : GoSlice) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fld rr go!"Durable" ↦□ false }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"recordCommands"))
        (Val #cs))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hrr, #Hd⟩
  wp_auto
  wp_end

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos

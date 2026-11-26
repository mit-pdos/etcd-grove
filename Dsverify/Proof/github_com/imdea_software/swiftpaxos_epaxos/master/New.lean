/-
`master.New(5, 7501, cfg, logger)`: the fresh master (`masterFresh`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.master.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [master.Assumptions] [examples.epaxosnet.Assumptions]

set_option goose.wp.extras true in
theorem master.New.wp_proof : master.New.specM (GF := GF) := by
  intro cfg logger c
  wp_start as ⟨#Hcfg, %Hl, #Hlog⟩
  wp_auto
  wp_apply (wp_slice_make3 (V := GoString) (W64 0) (W64 5) (by constructor <;> decide)) as %nl ⟨Hnl, Hnlc, %Hnlcap⟩
  wp_apply (wp_slice_make3 (V := GoString) (W64 0) (W64 5) (by constructor <;> decide)) as %al ⟨Hal, Halc, %Halcap⟩
  wp_apply (wp_slice_make3 (V := w64) (W64 0) (W64 5) (by constructor <;> decide)) as %pl ⟨Hpl, Hplc, %Hplcap⟩
  wp_apply (wp_slice_make2 (V := Loc) (W64 5)) $$ [] as %nds ⟨Hnds, -⟩
  · ipureintro; decide
  wp_apply (wp_slice_make2 (V := Bool) (W64 5)) $$ [] as %lds ⟨Hlds, -⟩
  · ipureintro; decide
  wp_apply (wp_slice_make2 (V := Bool) (W64 5)) $$ [] as %als ⟨Hals, -⟩
  · ipureintro; decide
  wp_apply (wp_slice_make2 (V := w64) (W64 5)) $$ [] as %lts ⟨Hlts, -⟩
  · ipureintro; decide
  wp_apply sync.wp_NewCond as %ic #Hic
  iapply HΦ
  unfold masterFresh
  iexists _, c
  iframe
  simp only [List.replicate_zero]
  iframe
  isplitr
  · ipureintro; simp only [Hnlcap, Halcap, Hplcap, true_and]; decide
  isplitl
  · iexact Hic
  iframe Hlog Hcfg
  ipureintro; exact Hl

end proof

end Perennial.github_com.imdea_software.swiftpaxos_epaxos

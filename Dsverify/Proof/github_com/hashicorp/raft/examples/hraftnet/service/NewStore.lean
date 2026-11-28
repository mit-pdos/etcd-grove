/-
The proof of `service.NewStore`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.service.NewStore

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

theorem github_com.hashicorp.raft.examples.hraftnet.service.NewStore.wp_proof : github_com.hashicorp.raft.examples.hraftnet.service.NewStore.spec (GF := GF) (hG := hG) := by
  intro γ fc i
  wp_start as ⟨#Hfr, #Hls, #Hdb⟩
  ihave Ha := mono_nat_own_alloc (GF := GF) 0
  imod Ha with ⟨%alb, Halb, -⟩
  ihave ⟨Halb1, Halb2⟩ := monoNat_split alb 0 $$ Halb
  ihave Hl := monoListLbOwn_nil (GF := GF) (A := Entry) fc.fr
  imod Hl with #Hlb
  iapply wp_fupd
  wp_auto
  iStructNamed «$r0»
  imod sync.init_Mutex (storeInv γ fc alb «$r0_ptr») ⊤ (structFieldRef Store go!"mu" «$r0_ptr») $$ [mu] [Halb2 present value index] with #Hmu
  · iexact mu
  · unfold storeInv
    inext
    iexists []
    iframe
    isplitr
    · unfold cIdxs; iapply BigSepL.bigSepL_nil.2; itrivial
    isplitr
    · unfold frLb; iexact Hlb
    ipureintro; exact ⟨by decide, lastCmd_nil⟩
  imodintro
  iapply HΦ
  iexists alb
  unfold isStore fsmOwn
  iframe Halb1
  iframe #

end proof

end Perennial

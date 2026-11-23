/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/dlog/Logger__Println.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`dlog.(*Logger).Println`'s proof: a non-verbose (`dlog.quiet`), non-nil logger does nothing.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Println

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [dlog.Assumptions]

set_option goose.wp.extras true

theorem dlog.Logger.Println.wp_proof : dlog.Logger.Println.spec (GF := GF) := fun l sl => by
  wp_start as Hq
  iunfold dlog.quiet at Hq
  icases Hq with ⟨%Hnn, #Hl⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  ihave Hl2 := Hl
  iStructNamed Hl2
  wp_auto
  iapply HΦ $$ %trivial

end proof

end Perennial.github_com.imdea_software.swiftpaxos

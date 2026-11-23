/-
`defs.NewDelayProposeChan` and `DelayProposeChan.Write` with no delay (`r.Dt` is nil, so the
delay is 0): a wrapper of the channel, whose `Write` sends on it (package-internal specs).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Specs
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos_epaxos.replica.defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

theorem wp_NewDelayProposeChan_zero (c : GoChan) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica.defs }}
      (App (App (Val (@! replica.defs.NewDelayProposeChan)) (Val #(W64 0))) (Val #c))
    {{ (dc : Loc), RET #dc; ∃ lc : GoChan,
        dc ↦ replica.defs.DelayProposeChan.mk (W64 0) c lc }} := by
  wp_start
  wp_auto
  iapply HΦ
  iexists _
  iexact «$r0»

/-- `dc.Write(g)` with no delay: `g` (with `P g`) is sent on the wrapped channel. -/
theorem wp_DelayProposeChan_Write_zero (dc : Loc) (c lc : GoChan) (g : Loc) (γc : ChanNames)
    (P : Loc → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica.defs ∗
        dc ↦□ replica.defs.DelayProposeChan.mk (W64 0) c lc ∗ isChanBag γc c P ∗ P g }}
      (App (Val (dc @!! go.GoType.PointerType replica.defs.DelayProposeChan.ty @!! go!"Write"))
        (Val #g))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hdc, #Hbag, HP⟩
  iStructNamed Hdc
  wp_auto
  wp_apply (wp_bag_send γc c g P) $$ [HP]
  · iframe; iframe #
  iapply HΦ; itrivial

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos

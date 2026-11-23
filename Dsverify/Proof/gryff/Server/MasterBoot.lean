/-
Ported in part from dsverify-lab examples/gryff/proof/GryffProof/Server/MasterBoot.lean (run
gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The kit's codec registration (`gryffnet.Register()`, `rpc_model_gen.go`: `rpcmodel.SetCodec` of
the generated `rpcEncode`/`rpcDecode`/`rpcReceiver`): `codecSet gryffCodec`, from the machine's
net/rpc boot resource (`rpcBootRes`, `RpcBootHyp`) and `Net/`'s `SetCodec.spec` (a premise,
discharged at linking). The rest of the lab's master boot (the node's boot over the lab's
harness: `master_boot'`) is the deployment's (`Mains`), over remote's machines.
-/
module

public import Dsverify.Proof.gryff.Server.MasterNew

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [kA : examples.gryffnet.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [H : RpcHttpHyp GF]
variable (wp_SetCodec : net.rpc.SetCodec.spec (GF := GF) (hG := hG))

set_option goose.wp.extras true

include wp_SetCodec in
/-- `gryffnet.Register()`: the kit's codec is registered, for good. -/
theorem wp_kit_Register :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗ rpcBootRes (GF := GF) }}
      (App (Val (@! examples.gryffnet.Register)) (Val #()))
    {{ RET #(); net.rpc.codecSet gryffCodec }} := by
  wp_start as Hb
  unfold rpcBootRes
  icases Hb with ⟨#Hsync, #Hmu, Hun, #Hinv⟩
  wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ «$a0» with ⟨«$a0», %Hnn⟩
  ipersist «$a0»
  wp_apply (wp_SetCodec gryffCodec «$a0_ptr») $$ [Hun] as #Hcs
  · iframe Hmu Hun
    isplitr
    · unfold net.rpc.codecIs
      iexists _
      iframe «$a0»
      dsimp only
      isplitr
      · iapply gryffCodec_encOk
      isplitr
      · iapply gryffCodec_decOk
      · iapply gryffCodec_rcvOk
    ipureintro; exact Hnn
  iapply HΦ; iframe #

end proof

end Perennial.gryff

/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/Register.lean (run gryff-bump-1, lab
master 915f964; notes/dsv-gryff.md).

The replica node's `rpc.Register(rep)` (`examples/gryffnet/kit.go`, `serve`: the node returns if
it fails, D17) for the one receiver the replica registers, `*gryff.Replica`, named `"Replica"`:
`nil` and the `"Replica"` service registered in `DefaultServer`'s registry, or an error.

Port (`Net/`): `rpc.Register` on `DefaultServer` is Net's `net.rpc.Register.spec` (rpc-defaultserver:
`Server.Register` on the package's `defaultServer`, proved in `Net/Proof/net/rpc/Register.lean`),
a premise here, linked at the top (`examples/gryffnet/Link.lean`); the receiver is `replicaOk`
(`B/Rcvr.lean`'s `replicaOk_intro`).
-/
module

public import Dsverify.Proof.gryff.B.Rcvr
public import Net.Spec.net.rpc.Register

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.unitB

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net
open Perennial.gryff

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [net.rpc.Assumptions] [net.FieldAssumptions]
variable (wp_Register : net.rpc.Register.spec (GF := GF) (hG := hG))

include wp_Register in
theorem wp_Register_replica (γ : GryffNames GF) (γs : GName) (rep : Loc) :
    {{ net.rpc.defaultServer γs ∗
        net.rpc.codecSet gryffCodec ∗ replicaOk γ rep }}
      (App (Val (@! net.rpc.Register)) (Val #(ptrIface src.gryff.Replica.ty rep)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ net.rpc.svcReg γs gryffCodec go!"Replica" replicaSvc) ∨
        ⌜err ≠ interface.nil⌝ }} := by
  iintro %Φ ⟨#Hds, #Hcs, Hok⟩ HΦ
  ihave Hok := replicaOk_rcvr γ rep $$ Hok
  iapply (wp_Register γs gryffCodec (ptrIface src.gryff.Replica.ty rep) replicaSvc
    go!"Replica" (W8 82) go!"eplica" rfl (by decide)) $$ [Hok] HΦ
  iframe Hok
  iframe #

end proof

end Perennial.gryff.unitB

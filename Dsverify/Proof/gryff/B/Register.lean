/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/Register.lean (run gryff-bump-1, lab
master 915f964; notes/dsv-gryff.md).

The replica node's `rpc.Register(rep)` (`examples/gryffnet/kit.go`, `serve`: the node returns if
it fails, D17) for the one receiver the replica registers, `*gryff.Replica`, named `"Replica"`:
`nil` and the `"Replica"` service registered in `DefaultServer`'s registry, or an error.

Port (`Net/`): `rpc.Register` on `DefaultServer` is `RpcHttpHyp.Register_spec` (net/rpc's
`Server.Register.spec` on the package's default server, a hypothesis until `Net/` gives net/rpc's
package initialization); the receiver is `replicaOk` (`B/Rcvr.lean`'s `replicaOk_intro`).
-/
module

public import Dsverify.Proof.gryff.B.Rcvr

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
variable [net.rpc.Assumptions] [net.FieldAssumptions] [RA : RpcHttpAddr GF] [H : RpcHttpHyp GF]

theorem wp_Register_replica (γ : GryffNames GF) (γs : GName) (rep : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ H.defaultServer γs ∗
        net.rpc.codecSet gryffCodec ∗ replicaOk γ rep }}
      (App (Val (@! net.rpc.Register)) (Val #(ptrIface src.gryff.Replica.ty rep)))
    {{ (err : GoInterface), RET #err;
        (⌜err = interface.nil⌝ ∗ net.rpc.svcReg γs gryffCodec go!"Replica" replicaSvc) ∨
        ⌜err ≠ interface.nil⌝ }} := by
  iintro %Φ ⟨#Hrpc, #Hds, #Hcs, Hok⟩ HΦ
  ihave Hok := replicaOk_rcvr γ rep $$ Hok
  iapply (H.Register_spec γs gryffCodec (ptrIface src.gryff.Replica.ty rep) replicaSvc
    go!"Replica" (W8 82) go!"eplica" rfl (by decide)) $$ [Hok] HΦ
  iframe Hok
  iframe #

end proof

end Perennial.gryff.unitB

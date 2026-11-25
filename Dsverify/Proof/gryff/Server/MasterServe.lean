/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Server/MasterServe.lean (run
gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

`(*Master).Serve()`: `http.Serve(master.l, nil)` on the master's listener, through
`RpcHttpHyp.Serve_spec` (the net/http server on `DefaultServeMux`, which routes
`defaultRPCPath` to the master's net/rpc server: `masterOkDef`'s `muxHas`). Port: `Serve_spec`
returns on a listener error (the lab's harness `Serve` never returned), so the master's `Serve`
returns `()` with nothing.
-/
module

public import Dsverify.Proof.gryff.Server.MasterDefs
public import Dsverify.Proof.gryff.src.masterlib.Base
public import Dsverify.GeneratedProof.gryff.src.masterlib

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [mA : gryff.src.masterlib.Assumptions]
variable [net.rpc.Assumptions] [net.FieldAssumptions] [RA : RpcHttpAddr GF] [H : RpcHttpHyp GF]

set_option goose.wp.extras true

theorem wp_Master_Serve' (γ : GryffNames GF) (m : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.masterlib ∗ masterOkDef γ m }}
      (App (Val (m @!! go.GoType.PointerType gryff.src.masterlib.Master.ty @!! go!"Serve"))
        (Val #()))
    {{ RET #(); True }} := by
  wp_start as #Hok
  unfold masterOkDef
  iNamed Hok
  wp_auto
  wp_apply (H.Serve_spec γ.rpc masterRpcLis net.rpc.defaultRPCPath li l)
  · iframe #
    ipureintro; exact Hth
  iintro %err -
  wp_auto
  wp_end

end proof

end Perennial.gryff

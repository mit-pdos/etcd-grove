/-
**The kit client's `op`** (`KitSpecs.lean`'s `op.spec`): `Client/Op.lean`'s `wp_op` (notes/dsv-gryff.md).
Its `AllG` is the heap's (`GooseGlobalGS.gooseAllG`, the one `Client/Defs.lean`'s `sysSt` and
Gryff's ghost state use): this module has no `[AllG GF]` section variable.
-/
module

public import Dsverify.Proof.gryff.Client.Op

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Net
open github_com.mit_pdos.etcd_grove.examples.lib.remote

namespace gryff.examples.gryffnet

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : gryff.examples.gryffnet.Assumptions] [wire.BufioSpecs GF] [wire.BinaryVarintHyps GF]
variable [net.Assumptions] [net.FieldAssumptions] [nS : netN.NetSpecs GF] [ρ : RemoteGS]

theorem op.wp_proof : op.spec (GF := GF) (hG := hG) := by
  intro γ c sp mu cl i Φ hc
  exact wp_op γ c sp mu cl i Φ hc

end proof

end gryff.examples.gryffnet

end Perennial

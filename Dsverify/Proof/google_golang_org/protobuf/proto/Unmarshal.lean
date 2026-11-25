/-
**Trust-boundary axiom** (dsv-fix6, mit-pdos/etcd-grove#49 fix 6; first stated in fix 4): `proto.Unmarshal(b, m)` (protobuf-go v1.36.12) into a fresh message of QuePaxa's kinds
(`msg.unmarshalPre`): `nil` and the decoded message owned, or an error (the spec
`raxos.hyp.proto.Unmarshal.spec`, `Dsverify/Proof/raxos/Hyp.lean`). The field `unmarshal` of
QuePaxa's statement premise `raxos.hyp.PbHyp` until dsv-fix6, verbatim, over the narrowed
representation of `Msg.lean` (`stateOk`, sealed `rt*`). Reviews: `notes/axiom-review/dsv-fix4/quepaxa-pb.md`
(refuted the wide representation), `notes/axiom-review/dsv-fix6/quepaxa-pb.md` (this one).
-/
module

public import Dsverify.Proof.raxos.Hyp

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **Trust-boundary axiom** (the file header). -/
axiom raxos.hyp.proto.Unmarshal.wp_proof : raxos.hyp.proto.Unmarshal.spec (GF := GF) (hG := hG)

end ax

end Perennial

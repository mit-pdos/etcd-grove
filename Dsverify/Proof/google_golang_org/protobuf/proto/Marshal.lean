/-
**Trust-boundary axiom** (dsv-fix6, mit-pdos/etcd-grove#49 fix 6; first stated in fix 4): `proto.Marshal(m)` (protobuf-go v1.36.12) of a message of QuePaxa's kinds (`msg.marshalPre`,
`Dsverify/Proof/raxos/Msg.lean`): its encoding, or an error, the message's representation given
back (the spec `raxos.hyp.proto.Marshal.spec`, `Dsverify/Proof/raxos/Hyp.lean`, whose docstring
argues it: protobuf-go writes only the runtime fields `state` and `sizeCache`, atomically). The
field `marshal` of QuePaxa's statement premise `raxos.hyp.PbHyp` until dsv-fix6, verbatim, over the narrowed
representation of `Msg.lean` (`stateOk`, sealed `rt*`). Reviews: `notes/axiom-review/dsv-fix4/quepaxa-pb.md`
(refuted the wide representation), `notes/axiom-review/dsv-fix6/quepaxa-pb.md` (refuted: the
message's declaring package's init missing, counterexample C; since then each kind asks its
`isPkgInit`), `notes/axiom-review/dsv-fix6/quepaxa-pb-2.md` (fresh review of this statement:
**survives with a condition**: the packages declaring the message types, `raxos/replica/src` and
`raxos/proto/client`, have no hand-written package-level variable initializer or `init()`, which
could marshal before the generated `init` fills `file_*_msgTypes`; checked by
`etc/dsv/pb-init-check.py` in `etc/gates.sh`).
-/
module

public import Dsverify.Proof.raxos.Hyp

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **Trust-boundary axiom** (the file header). -/
axiom raxos.hyp.proto.Marshal.wp_proof : raxos.hyp.proto.Marshal.spec (GF := GF) (hG := hG)

end ax

end Perennial

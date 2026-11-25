/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4; `encoding/gob` is translated names
only in the part): `enc.Encode(v)` on a fresh encoder, `v` an `*MSync` whose every listing fits, over a writer appending to an abstract stream (`writeSink`): it writes a gob stream `bs` of some listing `m'` of `v` (`wireBytes m' bs`), in one or more `Write`s of consecutive pieces of it, stopping at the first failed `Write`, and returns that error or nil (the spec's header, `Dsverify/Spec/encoding/gob/Encoder__EncodeW.lean`, argues it from Go's `encoder.go`). Over the fixed vocabulary of `Vocab.lean` (`swiftLibsOf π`, for every
net protocol names `π`), the spec `encoding.gob.Encoder.EncodeW.spec` (`Dsverify/Spec/encoding/gob/Encoder__EncodeW.lean`): until
dsv-fix4 the field of swiftpaxos's statement premise `SwiftHyps` over the quantified libraries `l`.
Review: `notes/axiom-review/dsv-fix4/encoding-gob.md`.
-/
module

public import Dsverify.Proof.encoding.gob.Vocab
public import Dsverify.Spec.encoding.gob.Encoder__EncodeW

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

section ax
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions]

/-- **Trust-boundary axiom** (the file header). -/
axiom encoding.gob.Encoder.EncodeW.wp_proof (π : Net.NetProtoGS) :
  letI := encoding.gob.swiftLibsOf (GF := GF) π
  encoding.gob.Encoder.EncodeW.spec (GF := GF)

end ax

end Perennial

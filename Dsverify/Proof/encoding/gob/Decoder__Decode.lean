/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4; `encoding/gob` is translated names
only in the part): `dec.Decode(v)` on a fresh decoder over a `*bufio.Reader` (no read-ahead), `v` an `*MSync` holding the zero value: it reads some bytes `data` from the reader and, when it returns nil, `data` is the gob stream of a value `m` the stream held there (if it held one) and `*v` holds `m` up to the maps' order (the spec's header, `Dsverify/Spec/encoding/gob/Decoder__Decode.lean`, argues it from Go's `decoder.go`). Over the fixed vocabulary of `Vocab.lean` (`swiftLibsOf π`, for every
net protocol names `π`), the spec `encoding.gob.Decoder.Decode.spec` (`Dsverify/Spec/encoding/gob/Decoder__Decode.lean`): until
dsv-fix4 the field of swiftpaxos's statement premise `SwiftHyps` over the quantified libraries `l`.
Review: `notes/axiom-review/dsv-fix4/encoding-gob.md`.
-/
module

public import Dsverify.Proof.encoding.gob.Vocab
public import Dsverify.Spec.encoding.gob.Decoder__Decode

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
axiom encoding.gob.Decoder.Decode.wp_proof (π : Net.NetProtoGS) :
  letI := encoding.gob.swiftLibsOf (GF := GF) π
  encoding.gob.Decoder.Decode.spec (GF := GF)

end ax

end Perennial

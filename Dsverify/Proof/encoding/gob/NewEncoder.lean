/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4; `encoding/gob` is translated names
only in the part): `NewEncoder(w)` returns a fresh `*Encoder` writing to `w` (`encoderTok`). Go's `encoder.go`: `NewEncoder` allocates the encoder and its maps and sets its writer list to `[w]`; no panic for any `w`. Over the fixed vocabulary of `Vocab.lean` (`swiftLibsOf π`, for every
net protocol names `π`), the spec `encoding.gob.NewEncoder.spec` (`Dsverify/Spec/encoding/gob/NewEncoder.lean`): until
dsv-fix4 the field of swiftpaxos's statement premise `SwiftHyps` over the quantified libraries `l`.
Review: `notes/axiom-review/dsv-fix4/encoding-gob.md`.
-/
module

public import Dsverify.Proof.encoding.gob.Vocab
public import Dsverify.Spec.encoding.gob.NewEncoder

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
axiom encoding.gob.NewEncoder.wp_proof (π : Net.NetProtoGS) :
  letI := encoding.gob.swiftLibsOf (GF := GF) π
  encoding.gob.NewEncoder.spec (GF := GF)

end ax

end Perennial

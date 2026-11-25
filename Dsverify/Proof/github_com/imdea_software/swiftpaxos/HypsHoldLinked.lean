/-
swiftpaxos's library classes (`Hyps.lean`: `SwiftHyps`, `SwiftOsRandom`; until dsv-fix4 premises
of its statement, over quantified libraries `l`) **hold** at the fixed libraries
`encoding.gob.swiftLibsOf π` (`Dsverify/Proof/encoding/gob/Vocab.lean`), from the per-function
trust-boundary axioms of `encoding/gob` (`Dsverify/Proof/encoding/gob/`) and `google/uuid`
(`Dsverify/Proof/github_com/google/uuid/`). A linking module: the kit's top-level proof discharges
the former premises with these.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.encoding.gob.NewEncoder
public import Dsverify.Proof.encoding.gob.NewDecoder
public import Dsverify.Proof.encoding.gob.Encoder__EncodeW
public import Dsverify.Proof.encoding.gob.Decoder__Decode
public import Dsverify.Proof.github_com.google.uuid.New
public import Dsverify.Proof.github_com.google.uuid.UUID__ID

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp

section holds
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **`SwiftHyps` holds** at the fixed libraries (a theorem, not an instance). -/
theorem swiftHyps_holds (π : Net.NetProtoGS) :
    letI := encoding.gob.swiftLibsOf (GF := GF) π; SwiftHyps GF := by
  letI := encoding.gob.swiftLibsOf (GF := GF) π
  exact ⟨fun {_} => encoding.gob.NewEncoder.wp_proof π, fun {_} => encoding.gob.NewDecoder.wp_proof π,
    fun {_} => encoding.gob.Encoder.EncodeW.wp_proof π,
    fun {_} => encoding.gob.Decoder.Decode.wp_proof π,
    fun {_} => github_com.google.uuid.UUID.ID.wp_proof⟩

/-- **`SwiftOsRandom` holds** at the fixed libraries (a theorem, not an instance). -/
theorem swiftOsRandom_holds (π : Net.NetProtoGS) :
    letI := encoding.gob.swiftLibsOf (GF := GF) π; SwiftOsRandom GF := by
  letI := encoding.gob.swiftLibsOf (GF := GF) π
  exact ⟨github_com.google.uuid.New.wp_proof⟩

end holds

end Perennial.github_com.imdea_software.swiftpaxos

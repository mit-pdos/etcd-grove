/-
**The library hypotheses** (notes/dsv-swiftpaxos.md, "Hypotheses"): the specs of the libraries the
swiftpaxos proof uses that have no proof here, one field each of `SwiftHyps`, named after the lab's
theorem it stands for; and, below, the lab's theorem names restated from the fields (as `X.wp_hyp` where the lab had `X.wp_proof`, so that this stays a defs module for the import tiers), so that the
ported proof reads as the lab's (`bufio.wp_ReadFull`, `treemap.Map.wp_Put`, …). A proof that uses one
has `[SwiftHyps netDistGF]` among its variables; `swiftpaxos_remote_robust` takes `SwiftHyps` at
every heap.

`SwiftHyps` is a `Prop`-valued class over a machine's heap, its Go semantics and its package
states (`SwiftNetPkgState`, which holds the libraries' representation predicates, `SwiftLibs`);
each field quantifies over the packages' `Assumptions` it needs. The gob specs are over the real
`encoding/gob`'s format, `sp.GobFmt` (a parent of `SwiftLibs`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.NetRpc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.BufioNet
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.NetLab
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.LibSpecs
public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Specs
public import Dsverify.Spec.encoding.gob.NewEncoder
public import Dsverify.Spec.encoding.gob.NewDecoder
public import Dsverify.Spec.encoding.gob.Encoder__EncodeW
public import Dsverify.Spec.encoding.gob.Decoder__Decode

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has

namespace github_com.imdea_software.swiftpaxos

/-- The library hypotheses: see the file header. -/
class SwiftHyps [go_gctx : GoGlobalContext] (GF : BundledGFunctors) [hG : HeapGS HasLC.hasLC GF]
    [sem : go.Semantics] [SwiftNetPkgState GF] : Prop where
  /-- lab `Proof/treemap/NewWith.lean` `treemap.NewWith.wp_proof` -/
  treemap_NewWith : ∀ [github_com.emirpasic.gods.maps.treemap.Assumptions],
    github_com.emirpasic.gods.maps.treemap.NewWith.spec (GF := GF)
  /-- lab `treemap.Map.Put.wp_proof` -/
  treemap_Put : ∀ [github_com.emirpasic.gods.maps.treemap.Assumptions],
    github_com.emirpasic.gods.maps.treemap.Map.Put.spec (GF := GF)
  /-- lab `treemap.Map.Get.wp_proof` -/
  treemap_Get : ∀ [github_com.emirpasic.gods.maps.treemap.Assumptions],
    github_com.emirpasic.gods.maps.treemap.Map.Get.spec (GF := GF)
  /-- lab `Spec/gob/NewEncoder.lean` `encoding.gob.NewEncoder.wp_proof`, over the real gob
  (`sp.GobFmt`; Spec/encoding/gob/Defs.lean) -/
  gob_NewEncoder : ∀ [examples.swiftnet.Assumptions], encoding.gob.NewEncoder.spec (GF := GF)
  /-- lab `encoding.gob.NewDecoder.wp_proof` -/
  gob_NewDecoder : ∀ [examples.swiftnet.Assumptions], encoding.gob.NewDecoder.spec (GF := GF)
  /-- lab `encoding.gob.Encoder.EncodeW.wp_proof` -/
  gob_EncodeW : ∀ [examples.swiftnet.Assumptions], encoding.gob.Encoder.EncodeW.spec (GF := GF)
  /-- lab `encoding.gob.Decoder.Decode.wp_proof` -/
  gob_Decode : ∀ [examples.swiftnet.Assumptions], encoding.gob.Decoder.Decode.spec (GF := GF)

  /-- lab `Harness/Proof/math/rand.lean` `math.rand.NewSource.wp_proof` (lib/LibSpecs.lean) -/
  math_rand_NewSource : math.rand.NewSource.spec (GF := GF)
  /-- lab `math.rand.New.wp_proof` -/
  math_rand_New : ∀ [math.rand.Assumptions], math.rand.New.spec (GF := GF)
  /-- lab `math.rand.Intn.wp_proof` -/
  math_rand_Intn : math.rand.Intn.spec (GF := GF)
  /-- lab `uuid.wp_ID` (`uuid.wp_New` is the environment class `SwiftOsRandom`, below) -/
  uuid_ID : ∀ [github_com.google.uuid.Assumptions], github_com.google.uuid.UUID.ID.spec (GF := GF)

/-- **The environment assumption** (not a library spec; dsv-rabia's `os.signal.NoSignals`): no
signal is sent to the deployment's processes, so the channel `hook.HookUser1` registers for
`SIGUSR1` never receives one (`lib/LibSpecs.lean`, `os.signal.NotifyQuiet.spec`). A premise of
`swiftpaxos_remote_robust` beside the library hypotheses, kept apart from them. -/
class SwiftNoSignals [go_gctx : GoGlobalContext] (GF : BundledGFunctors)
    [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [SwiftNetPkgState GF] : Prop where
  notifyQuiet : os.signal.NotifyQuiet.spec (GF := GF)

/-- **The environment assumption on the OS's randomness** (not a library spec): reading
`crypto/rand.Reader` does not fail, so `uuid.New()` (`Must(NewRandom())`, which panics when it
fails) returns (`lib/LibSpecs.lean`, `github_com.google.uuid.New.spec`, lab `uuid.wp_New`). A
premise of `swiftpaxos_remote_robust` beside the library hypotheses and `SwiftNoSignals`, kept
apart from them. -/
class SwiftOsRandom [go_gctx : GoGlobalContext] (GF : BundledGFunctors)
    [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [SwiftNetPkgState GF] : Prop where
  uuid_New : github_com.google.uuid.New.spec (GF := GF)

end github_com.imdea_software.swiftpaxos

/-! ## The lab's names -/

section names
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]
variable [h : github_com.imdea_software.swiftpaxos.SwiftHyps GF]

namespace bufio
variable [bufio.Assumptions] [io.Assumptions]
  [github_com.imdea_software.swiftpaxos.SwiftBufioDeps GF]
theorem wp_NewReader : NewReader.labSpec (GF := GF) := NewReader.labProof
theorem wp_ReadByte : Reader.ReadByte.labSpec (GF := GF) := Reader.ReadByte.labProof
theorem wp_Read : Reader.Read.labSpec (GF := GF) := Reader.Read.labProof
theorem wp_NewWriter : NewWriter.labSpec (GF := GF) := NewWriter.labProof
theorem wp_Flush : Writer.Flush.labSpec (GF := GF) := Writer.Flush.labProof
theorem wp_WriteByte : Writer.WriteByte.labSpec (GF := GF) := Writer.WriteByte.labProof
theorem wp_Write : Writer.Write.labSpec (GF := GF) := Writer.Write.labProof
theorem wp_ReadAtLeast : io.ReadAtLeast.labSpec (GF := GF) := io.ReadAtLeast.labProof
theorem wp_ReadFull : io.ReadFull.labSpec (GF := GF) := io.ReadFull.labProof
theorem wp_WriteByte_err : Writer.WriteByte_err.labSpec (GF := GF) := Writer.WriteByte_err.labProof
theorem wp_Write_err : Writer.Write_err.labSpec (GF := GF) := Writer.Write_err.labProof
theorem wp_ReadByte_wf : Reader.ReadByte_wf.labSpec (GF := GF) := Reader.ReadByte_wf.labProof

end bufio

namespace github_com.emirpasic.gods.maps.treemap
variable [treemap.Assumptions]
theorem wp_NewWith : NewWith.spec (GF := GF) := h.treemap_NewWith
theorem Map.wp_Put : Map.Put.spec (GF := GF) := h.treemap_Put
theorem Map.wp_Get : Map.Get.spec (GF := GF) := h.treemap_Get
end github_com.emirpasic.gods.maps.treemap

namespace encoding.gob
variable [github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions]
theorem NewEncoder.wp_hyp : NewEncoder.spec (GF := GF) := h.gob_NewEncoder
theorem NewDecoder.wp_hyp : NewDecoder.spec (GF := GF) := h.gob_NewDecoder
theorem Encoder.EncodeW.wp_hyp : Encoder.EncodeW.spec (GF := GF) := h.gob_EncodeW
theorem Decoder.Decode.wp_hyp : Decoder.Decode.spec (GF := GF) := h.gob_Decode
end encoding.gob

namespace math.rand
theorem NewSource.wp_hyp : NewSource.spec (GF := GF) := h.math_rand_NewSource
theorem New.wp_hyp [math.rand.Assumptions] : New.spec (GF := GF) := h.math_rand_New
theorem Intn.wp_hyp : Intn.spec (GF := GF) := h.math_rand_Intn
end math.rand

theorem os.signal.NotifyQuiet.wp_hyp [hs : github_com.imdea_software.swiftpaxos.SwiftNoSignals GF] :
    os.signal.NotifyQuiet.spec (GF := GF) := hs.notifyQuiet

namespace github_com.google.uuid
theorem wp_New [hr : github_com.imdea_software.swiftpaxos.SwiftOsRandom GF] : New.spec (GF := GF) :=
  hr.uuid_New
theorem wp_ID [github_com.google.uuid.Assumptions] : UUID.ID.spec (GF := GF) := h.uuid_ID
end github_com.google.uuid

end names

end Perennial

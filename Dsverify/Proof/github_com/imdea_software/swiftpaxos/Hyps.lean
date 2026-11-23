/-
**The library hypotheses** (notes/dsv-swiftpaxos.md, "Hypotheses"): the specs of the libraries the
swiftpaxos proof uses that have no proof here, one field each of `SwiftHyps`, named after the lab's
theorem it stands for; and, below, the lab's theorem names restated from the fields, so that the
ported proof reads as the lab's (`bufio.wp_ReadFull`, `treemap.Map.wp_Put`, …). A proof that uses one
has `[SwiftHyps netDistGF]` among its variables; `swiftpaxos_remote_robust` takes `SwiftHyps` at
every heap.

`SwiftHyps` is a `Prop`-valued class over a machine's heap, its Go semantics and its package
states (`SwiftNetPkgState`, which holds the libraries' representation predicates, `SwiftLibs`);
each field quantifies over the packages' `Assumptions` it needs, and the gob specs over the codec.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.NetRpc
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.BufioNet
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.NetLab
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.LibSpecs
public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Specs
public import Dsverify.Spec.encoding.gob.NewEncoder
public import Dsverify.Spec.encoding.gob.NewDecoder
public import Dsverify.Spec.encoding.gob.Encoder__Encode
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
  /-- lab `Harness/Proof/bufio/Reader.lean` `bufio.wp_NewReader` -/
  bufio_NewReader : ∀ [bufio.Assumptions] [io.Assumptions], bufio.NewReader.labSpec (GF := GF)
  /-- lab `bufio.wp_ReadByte` -/
  bufio_ReadByte : ∀ [bufio.Assumptions] [io.Assumptions], bufio.Reader.ReadByte.labSpec (GF := GF)
  /-- lab `bufio.wp_Read` -/
  bufio_Read : ∀ [bufio.Assumptions] [io.Assumptions], bufio.Reader.Read.labSpec (GF := GF)
  /-- lab `Harness/Proof/bufio/ReadFull.lean` `bufio.wp_ReadAtLeast` (`io.ReadAtLeast`) -/
  bufio_ReadAtLeast : ∀ [bufio.Assumptions] [io.Assumptions],
    bufio.io.ReadAtLeast.labSpec (GF := GF)
  /-- lab `bufio.wp_ReadFull` (`io.ReadFull`) -/
  bufio_ReadFull : ∀ [bufio.Assumptions] [io.Assumptions], bufio.io.ReadFull.labSpec (GF := GF)
  /-- lab `bufio.wp_ReadByte_wf` -/
  bufio_ReadByte_wf : ∀ [bufio.Assumptions] [io.Assumptions],
    bufio.Reader.ReadByte_wf.labSpec (GF := GF)
  /-- lab `Proof/treemap/NewWith.lean` `treemap.NewWith.wp_proof` -/
  treemap_NewWith : ∀ [github_com.emirpasic.gods.maps.treemap.Assumptions],
    github_com.emirpasic.gods.maps.treemap.NewWith.spec (GF := GF)
  /-- lab `treemap.Map.Put.wp_proof` -/
  treemap_Put : ∀ [github_com.emirpasic.gods.maps.treemap.Assumptions],
    github_com.emirpasic.gods.maps.treemap.Map.Put.spec (GF := GF)
  /-- lab `treemap.Map.Get.wp_proof` -/
  treemap_Get : ∀ [github_com.emirpasic.gods.maps.treemap.Assumptions],
    github_com.emirpasic.gods.maps.treemap.Map.Get.spec (GF := GF)
  /-- lab `Spec/gob/NewEncoder.lean` `encoding.gob.NewEncoder.wp_proof` -/
  gob_NewEncoder : ∀ [examples.swiftnet.Assumptions] [net.Assumptions] [net.FieldAssumptions]
    [net.rpc.Assumptions] [net.rpc.RpcCodec GF], encoding.gob.NewEncoder.spec (GF := GF)
  /-- lab `encoding.gob.NewDecoder.wp_proof` -/
  gob_NewDecoder : ∀ [examples.swiftnet.Assumptions] [net.Assumptions] [net.FieldAssumptions]
    [net.rpc.Assumptions] [net.rpc.RpcCodec GF], encoding.gob.NewDecoder.spec (GF := GF)
  /-- lab `encoding.gob.Encoder.Encode.wp_proof` -/
  gob_Encode : ∀ [examples.swiftnet.Assumptions] [net.Assumptions] [net.FieldAssumptions]
    [net.rpc.Assumptions] [net.rpc.RpcCodec GF], encoding.gob.Encoder.Encode.spec (GF := GF)
  /-- lab `encoding.gob.Encoder.EncodeW.wp_proof` -/
  gob_EncodeW : ∀ [examples.swiftnet.Assumptions] [net.Assumptions] [net.FieldAssumptions]
    [net.rpc.Assumptions] [net.rpc.RpcCodec GF], encoding.gob.Encoder.EncodeW.spec (GF := GF)
  /-- lab `encoding.gob.Decoder.Decode.wp_proof` -/
  gob_Decode : ∀ [examples.swiftnet.Assumptions] [net.Assumptions] [net.FieldAssumptions]
    [net.rpc.Assumptions] [net.rpc.RpcCodec GF], encoding.gob.Decoder.Decode.spec (GF := GF)

  /-- lab `Harness/Proof/math/rand.lean` `math.rand.NewSource.wp_proof` (lib/LibSpecs.lean) -/
  math_rand_NewSource : math.rand.NewSource.spec (GF := GF)
  /-- lab `math.rand.New.wp_proof` -/
  math_rand_New : ∀ [math.rand.Assumptions], math.rand.New.spec (GF := GF)
  /-- lab `math.rand.Intn.wp_proof` -/
  math_rand_Intn : math.rand.Intn.spec (GF := GF)
  /-- lab `Harness/Proof/os/signal.lean` `os.signal.Notify.wp_proof` (an assumption of the
  deployment: lib/LibSpecs.lean's header) -/
  os_signal_Notify : os.signal.Notify.spec (GF := GF)
  /-- lab `Harness/Proof/uuid/Specs.lean` `uuid.wp_New` -/
  uuid_New : github_com.google.uuid.New.spec (GF := GF)
  /-- lab `uuid.wp_ID` -/
  uuid_ID : ∀ [github_com.google.uuid.Assumptions], github_com.google.uuid.UUID.ID.spec (GF := GF)

end github_com.imdea_software.swiftpaxos

/-! ## The lab's names -/

section names
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]
variable [h : github_com.imdea_software.swiftpaxos.SwiftHyps GF]

namespace bufio
variable [bufio.Assumptions] [io.Assumptions]
theorem wp_NewReader : NewReader.labSpec (GF := GF) := h.bufio_NewReader
theorem wp_ReadByte : Reader.ReadByte.labSpec (GF := GF) := h.bufio_ReadByte
theorem wp_Read : Reader.Read.labSpec (GF := GF) := h.bufio_Read
theorem wp_NewWriter : NewWriter.labSpec (GF := GF) := NewWriter.labProof
theorem wp_Flush : Writer.Flush.labSpec (GF := GF) := Writer.Flush.labProof
theorem wp_WriteByte : Writer.WriteByte.labSpec (GF := GF) := Writer.WriteByte.labProof
theorem wp_Write : Writer.Write.labSpec (GF := GF) := Writer.Write.labProof
theorem wp_ReadAtLeast : io.ReadAtLeast.labSpec (GF := GF) := h.bufio_ReadAtLeast
theorem wp_ReadFull : io.ReadFull.labSpec (GF := GF) := h.bufio_ReadFull
theorem wp_WriteByte_err : Writer.WriteByte_err.labSpec (GF := GF) := Writer.WriteByte_err.labProof
theorem wp_Write_err : Writer.Write_err.labSpec (GF := GF) := Writer.Write_err.labProof
theorem wp_ReadByte_wf : Reader.ReadByte_wf.labSpec (GF := GF) := h.bufio_ReadByte_wf

/-- The lab's `bufio.bufioReadsOk` (`Harness/Proof/bufio/ReadFull.lean`): a `*bufio.Reader` (as an
`io.Reader`) reads its stream, from `wp_Read`. -/
theorem bufioReadsOk (br : Loc) (rd : GoInterface) (I : List w8 → IProp GF) :
    (isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ readerOk rd I) ⊢
      readsOk (interface.mkOk (go.GoType.PointerType bufio.Reader.ty) #br) (ownReader br rd I) := by
  iintro ⟨#Hpkg, #Hrd⟩
  unfold readsOk
  iexists interface.mk (go.GoType.PointerType bufio.Reader.ty) #br
  isplitr
  · ipureintro; rfl
  imodintro
  iintro %b %bs %R %Φ %Hpos Hown Hb HΦ
  wp_apply wp_Read br rd I R b bs $$ [$Hpkg $Hrd $Hown $Hb] as %n %err ⟨%data, %Hd, Hb, Hown, #He⟩
  obtain ⟨rfl, hdl⟩ := Hd
  iapply HΦ $$ %data %err %hdl Hb [Hown] He
  inext; iexact Hown
end bufio

namespace github_com.emirpasic.gods.maps.treemap
variable [treemap.Assumptions]
theorem wp_NewWith : NewWith.spec (GF := GF) := h.treemap_NewWith
theorem Map.wp_Put : Map.Put.spec (GF := GF) := h.treemap_Put
theorem Map.wp_Get : Map.Get.spec (GF := GF) := h.treemap_Get
end github_com.emirpasic.gods.maps.treemap

namespace encoding.gob
variable [github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions] [net.Assumptions]
  [net.FieldAssumptions] [net.rpc.Assumptions] [net.rpc.RpcCodec GF]
theorem NewEncoder.wp_proof : NewEncoder.spec (GF := GF) := h.gob_NewEncoder
theorem NewDecoder.wp_proof : NewDecoder.spec (GF := GF) := h.gob_NewDecoder
theorem Encoder.Encode.wp_proof : Encoder.Encode.spec (GF := GF) := h.gob_Encode
theorem Encoder.EncodeW.wp_proof : Encoder.EncodeW.spec (GF := GF) := h.gob_EncodeW
theorem Decoder.Decode.wp_proof : Decoder.Decode.spec (GF := GF) := h.gob_Decode
end encoding.gob

namespace math.rand
theorem NewSource.wp_proof : NewSource.spec (GF := GF) := h.math_rand_NewSource
theorem New.wp_proof [math.rand.Assumptions] : New.spec (GF := GF) := h.math_rand_New
theorem Intn.wp_proof : Intn.spec (GF := GF) := h.math_rand_Intn
end math.rand

theorem os.signal.Notify.wp_proof : os.signal.Notify.spec (GF := GF) := h.os_signal_Notify

namespace github_com.google.uuid
theorem wp_New : New.spec (GF := GF) := h.uuid_New
theorem wp_ID [github_com.google.uuid.Assumptions] : UUID.ID.spec (GF := GF) := h.uuid_ID
end github_com.google.uuid

end names

end Perennial

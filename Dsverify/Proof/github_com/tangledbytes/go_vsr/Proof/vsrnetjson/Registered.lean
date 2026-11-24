/-
**`vsrnet.registeredCodecOk`, proved** (it was a premise of vr's statement, a field of `JsonHyps`
until round 8): the kit's registered codec meets `codecPart vsrnet.jsonCodec`, its `Marshal`
(`RegMarshal.lean`) and its `Unmarshal` (`RegUnmarshal.lean`), from the specs of `jsoncodec`'s
helpers (`Net/Spec/models_lab/jsoncodec/`); `examples/vsrnet/Link.lean` passes their proofs
(`Net/Proof/models_lab/Results.lean`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrnetjson.RegMarshal
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrnetjson.RegUnmarshal

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [vsrnet.Assumptions]

/-- The registered codec meets `codecPart vsrnet.jsonCodec`, from the `jsoncodec` helpers' specs. -/
theorem vsrnet.registeredCodecOk_of
    (wp_AppendRaw : models_lab.jsoncodec.AppendRaw.spec (GF := GF) (hG := hG))
    (wp_AppendQuotedUint : models_lab.jsoncodec.AppendQuotedUint.spec (GF := GF) (hG := hG))
    (wp_AppendString : models_lab.jsoncodec.AppendString.spec (GF := GF) (hG := hG))
    (wp_At : models_lab.jsoncodec.At.spec (GF := GF) (hG := hG))
    (wp_Empty : models_lab.jsoncodec.Empty.spec (GF := GF) (hG := hG))
    (wp_Member : models_lab.jsoncodec.Member.spec (GF := GF) (hG := hG))
    (wp_Next : models_lab.jsoncodec.Next.spec (GF := GF) (hG := hG))
    (wp_String : models_lab.jsoncodec.String.spec (GF := GF) (hG := hG))
    (wp_QuotedUint : models_lab.jsoncodec.QuotedUint.spec (GF := GF) (hG := hG)) :
    vsrnet.registeredCodecOk (GF := GF) (hG := hG) := by
  unfold vsrnet.registeredCodecOk
  ihave #Hm := vsrnet.registeredMarshalOk wp_AppendRaw wp_AppendQuotedUint wp_AppendString
  ihave #Hu := vsrnet.registeredUnmarshalOk wp_At wp_Empty wp_Member wp_Next wp_String
    wp_QuotedUint
  isplitl []
  · iexact Hm
  · iexact Hu

end proof

end Perennial.github_com.tangledbytes.go_vsr.examples

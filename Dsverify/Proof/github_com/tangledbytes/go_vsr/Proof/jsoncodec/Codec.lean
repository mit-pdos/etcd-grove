/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/jsoncodec/Codec.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the class is `models_lab.jsoncodec.JsonCodec`;
the lab's `VsrNetPkgState` argument of the cases is gone (package facts are the packages' `Base.lean`),
`encoding.json.Assumptions` is carried inside the cases that mention `codecSet` (which needs it here).
-/
/-
The kit's codec as the specs see it (`vsrnet.jsonCodec`): what `Marshal(v)` and
`Unmarshal(bs, ptr)` are given (`encP`, `decP`). Each is a disjunction over the values the
program encodes and decodes: an event (`*events.Event`) and a `[]log.Log` (encoding); a
`vsrwire.Frame` (a line), a payload (`*events.<T>`) and a `[]log.Log` (decoding). The
packages' `Assumptions` and package state the cases need are carried inside (the codec's
instance is stated without them).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.events

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section codec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- `Marshal(v)`'s deposit: `v` is an event of a message with plain strings (encoded as
`encEvent m`), or a `[]log.Log` with plain operations (encoded as `encLogs es`). -/
def vsrnet.encP (v : GoInterface) (Ψ : Option (List w8) → IProp GF) : IProp GF :=
  iprop(
    (∃ (_ : pkg.log.Assumptions) (_ : pkg.events.Assumptions) (_ : encoding.json.Assumptions)
        (ev : Loc) (m : Msg),
      ⌜v = interface.mkOk (go.GoType.PointerType pkg.events.Event.ty) #ev⌝ ∗ ⌜PlainMsg m⌝ ∗
      isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
      encoding.json.codecSet (GF := GF) ∗ pkg.events.isEvent ev m ∗
      Ψ (some (VsrWire.encEvent m))) ∨
    (∃ (_ : pkg.log.Assumptions) (sl : GoSlice) (dq : DFrac) (es : List Entry),
      ⌜v = interface.mkOk (go.GoType.SliceType pkg.log.Log.ty) #sl⌝ ∗
      ⌜∀ e ∈ es, PlainStr e.op⌝ ∗ pkg.log.ownLogs sl dq es ∗
      (pkg.log.ownLogs sl dq es -∗ Ψ (some (pkg.log.encLogs es)))))

/-- `Unmarshal(bs, ptr)`'s deposit: `bs` is a line's value after whitespace and `ptr` a
`*vsrwire.Frame` with nil `Data`; or `bs` is a payload and `ptr` points to a zero value of its
type; or `bs` is a `[]log.Log`'s encoding and `ptr` a `*[]log.Log` holding nil. -/
def vsrnet.decP (bs : List w8) (ptr : GoInterface) (Ψ : Bool → IProp GF) :
    IProp GF :=
  iprop(
    (∃ (_ : vsrwire.Assumptions) (ws : List w8) (m : Msg) (p : Loc) (fr : vsrwire.Frame),
      ⌜bs = ws ++ VsrWire.encEvent m⌝ ∗ ⌜∀ c ∈ ws, encoding.json.isSpaceB c = true⌝ ∗
      ⌜PlainMsg m⌝ ∗ ⌜fr.Data' = slice.nil⌝ ∗
      ⌜ptr = interface.mkOk (go.GoType.PointerType vsrwire.Frame.ty) #p⌝ ∗ p ↦ fr ∗
      (∀ data : GoSlice, p ↦ vsrwire.Frame.mk (pkg.events.typeOf m) data ∗
        data ↦* pkg.events.encPayload m ∗ ownSliceCap w8 data (DFrac.own 1) -∗ Ψ true)) ∨
    (∃ (_ : pkg.log.Assumptions) (_ : pkg.events.Assumptions) (_ : encoding.json.Assumptions)
        (m : Msg) (p : Loc),
      ⌜bs = pkg.events.encPayload m⌝ ∗ ⌜PlainMsg m⌝ ∗ ⌜MsgBound m⌝ ∗
      ⌜ptr = interface.mkOk (go.GoType.PointerType (pkg.events.payloadTy m)) #p⌝ ∗
      isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
      encoding.json.codecSet (GF := GF) ∗ pkg.events.payloadZero p m ∗
      (pkg.events.payloadAt p m -∗ Ψ true)) ∨
    (∃ (_ : pkg.log.Assumptions) (es : List Entry) (p : Loc),
      ⌜bs = pkg.log.encLogs es⌝ ∗ ⌜∀ e ∈ es, e.cid < 2 ^ 64 ∧ e.req < 2 ^ 64 ∧ PlainStr e.op⌝ ∗
      ⌜ptr = interface.mkOk (go.GoType.PointerType (go.GoType.SliceType pkg.log.Log.ty)) #p⌝ ∗
      p ↦ slice.nil ∗
      (∀ sl : GoSlice, p ↦ sl ∗ pkg.log.ownLogs sl (DFrac.own 1) es ∗
        ownSliceCap pkg.log.Log sl (DFrac.own 1) -∗ Ψ true)))

/-- The codec (`vsrnet.jsonCodec` is this). -/
def vsrnet.codecInst : models_lab.jsoncodec.JsonCodec GF := ⟨vsrnet.encP, vsrnet.decP⟩

end codec

end Perennial.github_com.tangledbytes.go_vsr.examples

/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Spec/vsrwire.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; `init0.spec` takes `hookKnownFull` (the lab's
`hookKnown`, `Spec/events.lean`).
-/
/-
Cross-package spec of `examples/vsrwire` (the G1 hook): `decodeFrame`, the function its `init`
installs (`events.SetFrameDecoder`), is a frame decoder (`events.frameDecOk`): it decodes the next
frame of a decoder's stream into a `Frame` (`dec.Decode(&f)`, `events.Decoder.Decode_frame`)
and returns its type and payload bytes. `init0`: `vsrwire`'s `init` sets the hook for good
(`events.frameDecoderSet`; the hook's lock, D11).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.events

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : vsrwire.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [π : NetProtoGS] [encoding.json.DecoderRep GF]
variable [encoding.json.Assumptions] [models_lab.jsoncodec.JsonCodec GF]

/-- `decodeFrame` is a frame decoder, once `encoding/json` is initialized (all it calls; so
`vsrwire`'s own `init` can use this when it sets the hook: `events.hookInv`). -/
abbrev vsrwire.decodeFrame.spec : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.encoding.json ⊢
    pkg.events.frameDecOk (functions vsrwire.decodeFrame [])

/-- `vsrwire`'s `init` (`events.SetFrameDecoder(decodeFrame)`; D11), `events` initialized
(its state: the hook's lock, `hookKnown`): the hook is set for good (`frameDecoderSet`,
`vsrwire`'s package state). What the top's `vsrwire.initialize'` proof uses. -/
abbrev vsrwire.init0.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.events ∗
      pkg.events.hookKnownFull }}
    (App (Val (@! vsrwire.init.«0»)) (Val #()))
  {{ RET #(); pkg.events.frameDecoderSet }}

end spec

end Perennial.github_com.tangledbytes.go_vsr.examples

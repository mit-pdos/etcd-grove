/-
The package fact of `github_com.tangledbytes.go_vsr.pkg.events` (the vr kit, notes/dsv-vr.md):
the frame-decoder hook's lock (`hookKnownFull`, the lab's `hookKnown`, D11): `frameDecoderMu`
holds, read-only for good, a mutex guarding `frameDecoder`, with a flag `γh` (a mono list: `[]`
unset, `[()]` set). What changed against the lab: the lock's invariant says which function a set
hook holds, `vsrwire`'s `decodeFrame` (`kitFrameDecoder`; the only caller of `SetFrameDecoder` is
`vsrwire`'s `init`), not that it meets the frame decoder's spec (the lab's `frameDecOk f`, a spec
over the codec's and the decoder's representations, `Spec/events.lean`): so the fact names no
class of the proof (`DecoderRep`, `JsonCodec`, `NetProtoGS`), and `FromDecoder`'s proof gets the
decoder's spec from `decodeFrame`'s (`Proof/vsrwire/Hook.lean`). `frameDecoderSet`, the hook set
for good, is `vsrwire`'s fact (`examples/vsrwire/Base.lean`).
-/
module

public import Net.Proof.net.Base
public import Dsverify.GeneratedProof.github_com.tangledbytes.go_vsr.pkg.events
public import Dsverify.Code.github_com.tangledbytes.go_vsr.examples.vsrwire
public import Proof.encoding.json.Base
public import Net.Proof.models_lab.jsoncodec.Base
public import Perennial.Proof.errors.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.sync.Base
public import Perennial.Ghost.MonoList
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.ipv4port.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.log.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.tangledbytes.go_vsr.pkg.events

/-- The frame decoder a set hook holds: `vsrwire`'s `decodeFrame`. -/
abbrev kitFrameDecoder [GooseExts] [GoSemanticsFunctions] [GoGlobalContext] : GoFunc :=
  functions examples.vsrwire.decodeFrame []

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : github_com.tangledbytes.go_vsr.pkg.events.Assumptions]

/-- The lock invariant of `frameDecoderMu` (D11), with the flag `γh`: `frameDecoder` holds `nil`
(unset), or `kitFrameDecoder` (set, for good: the flag's lower bound `[()]` rules the unset case
out). -/
def hookLockInvFull (γh : GName) : IProp GF :=
  iprop(∃ f : GoFunc, globalAddr frameDecoder ↦ f ∗
    ((⌜f = func.nil⌝ ∗ monoListAuthOwn γh 1 ([] : List Unit)) ∨
     (⌜f = kitFrameDecoder⌝ ∗ monoListAuthOwn γh 1 [()])))

/-- The hook's lock (persistent): `frameDecoderMu` holds a mutex guarding `frameDecoder`. -/
def hookState (γh : GName) : IProp GF :=
  iprop(∃ mu : Loc, globalAddr frameDecoderMu ↦□ mu ∗ sync.isMutex mu (hookLockInvFull γh))

/-- `events`' package fact (persistent): the hook's lock exists. -/
def hookKnownFull : IProp GF :=
  iprop(∃ γh : GName, hookState γh)

/-- The hook is set, for good, to `kitFrameDecoder` (persistent): the hook's lock and the
flag's lower bound; `vsrwire`'s package fact. -/
def frameDecoderSet : IProp GF :=
  iprop(∃ γh : GName, hookState γh ∗ monoListLbOwn γh [()])

instance hookState_persistent (γh : GName) : Persistent (hookState (GF := GF) γh) := by
  unfold hookState; infer_instance
instance hookKnownFull_persistent : Persistent (hookKnownFull (GF := GF)) := by
  unfold hookKnownFull; infer_instance
instance frameDecoderSet_persistent : Persistent (frameDecoderSet (GF := GF)) := by
  unfold frameDecoderSet; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.events :=
  define_is_pkg_init (hookKnownFull (GF := GF))
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.events :=
  build_get_is_pkg_init_wf

end def_

end github_com.tangledbytes.go_vsr.pkg.events
end Perennial

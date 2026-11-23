/-
The package fact of `github_com.tangledbytes.go_vsr.pkg.events` (the vr kit, notes/dsv-vr.md):
the frame-decoder hook's lock (`hookKnown`, the lab's `events` package state, D11): `frameDecoderMu`
holds, read-only for good, a mutex guarding `frameDecoder`. For now the lock's invariant is only
that `frameDecoder` holds some function (the lab's also keeps the set decoder's spec and the flag
`γh`; added with the events proofs).
-/
module

public import Net.Proof.net.Base
public import Dsverify.GeneratedProof.github_com.tangledbytes.go_vsr.pkg.events
public import Dsverify.Proof.encoding.json.Base
public import Perennial.Proof.errors.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.sync.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.ipv4port.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.log.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.tangledbytes.go_vsr.pkg.events

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : github_com.tangledbytes.go_vsr.pkg.events.Assumptions]

/-- The hook's lock invariant (for now): `frameDecoder` holds some function. -/
def hookLockInv : IProp GF := iprop(∃ f : GoFunc, globalAddr frameDecoder ↦ f)

/-- The hook's lock (persistent): `frameDecoderMu` holds a mutex guarding `frameDecoder`. -/
def hookKnown : IProp GF :=
  iprop(∃ mu : Loc, globalAddr frameDecoderMu ↦□ mu ∗ sync.isMutex mu (hookLockInv (GF := GF)))

instance hookKnown_persistent : Persistent (hookKnown (GF := GF)) := by
  unfold hookKnown; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.events :=
  define_is_pkg_init (hookKnown (GF := GF))
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.events :=
  build_get_is_pkg_init_wf

end def_

end github_com.tangledbytes.go_vsr.pkg.events
end Perennial

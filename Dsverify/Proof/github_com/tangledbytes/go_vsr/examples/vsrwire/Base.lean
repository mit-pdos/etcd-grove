/-
The package fact of `github_com.tangledbytes.go_vsr.examples.vsrwire` (the vr kit, notes/dsv-vr.md): the hook set for good to `decodeFrame` (`events.frameDecoderSet`,
`pkg/events/Base.lean`; the lab's `frameDecoderSet`): what its `init` does.
-/
module

public import Net.Proof.net.Base
public import Dsverify.GeneratedProof.github_com.tangledbytes.go_vsr.examples.vsrwire
public import Dsverify.Proof.encoding.json.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.events.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.tangledbytes.go_vsr.examples.vsrwire

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : github_com.tangledbytes.go_vsr.examples.vsrwire.Assumptions]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrwire :=
  define_is_pkg_init (github_com.tangledbytes.go_vsr.pkg.events.frameDecoderSet (GF := GF))
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.examples.vsrwire :=
  build_get_is_pkg_init_wf

end def_

end github_com.tangledbytes.go_vsr.examples.vsrwire
end Perennial

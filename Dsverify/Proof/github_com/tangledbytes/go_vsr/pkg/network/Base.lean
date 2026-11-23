/-
The package fact of `github_com.tangledbytes.go_vsr.pkg.network` (the vr kit, notes/dsv-vr.md):
`ErrNoConn` holds `errors.New(noConnMsg)` for good (`errors.newVar`; the lab's `Top/PkgStates.lean`).
-/
module

public import Dsverify.GeneratedProof.github_com.tangledbytes.go_vsr.pkg.network
public import Perennial.Proof.io.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.events.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.ipv4port.Base
public import Proof.encoding.json.Base
public import Perennial.Proof.errors.Base
public import Dsverify.Proof.log.slog.Base
public import Net.Proof.net.Base
public import Perennial.Proof.sync.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.assert.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.queue.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.tangledbytes.go_vsr.pkg.network

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : github_com.tangledbytes.go_vsr.pkg.network.Assumptions]

/-- `ErrNoConn`'s message. -/
abbrev noConnMsg : GoString := go!"network: no connection to the source address"

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.network :=
  define_is_pkg_init (errors.newVar (GF := GF) ErrNoConn noConnMsg)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.network :=
  build_get_is_pkg_init_wf

end def_

end github_com.tangledbytes.go_vsr.pkg.network
end Perennial

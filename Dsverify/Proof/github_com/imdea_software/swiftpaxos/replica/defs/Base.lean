/-
The package fact of `github_com.imdea_software.swiftpaxos.replica.defs` (dsv-swiftpaxos, notes/dsv-swiftpaxos.md): `LatencyConf` holds `""` for good (the lab's `defs.pkgSt`; no code writes it).
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.replica.defs
public import Perennial.Proof.io.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Dsverify.Proof.bufio.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Init
public import Net.Proof.net.Init
public import Net.Proof.os.Init
public import Dsverify.Proof.encoding.json.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.imdea_software.swiftpaxos.replica.defs

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.replica.defs :=
  define_is_pkg_init iprop(globalAddr replica.defs.LatencyConf ↦□ ([] : GoString))
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.replica.defs :=
  build_get_is_pkg_init_wf

end def_

end github_com.imdea_software.swiftpaxos.replica.defs
end Perennial

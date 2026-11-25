/-
The package fact of `github_com.imdea_software.swiftpaxos.state` (dsv-swiftpaxos, notes/dsv-swiftpaxos.md): `True` (no variables).
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.state
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.sync.Link
public import Proof.encoding.hex.Init
public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Init
public import Proof.encoding.json.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.imdea_software.swiftpaxos.state

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.state :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.state :=
  build_get_is_pkg_init_wf

end def_

end github_com.imdea_software.swiftpaxos.state
end Perennial

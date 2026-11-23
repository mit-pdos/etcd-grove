/-
The package fact of `github_com.imdea_software.swiftpaxos.replica` (dsv-swiftpaxos, notes/dsv-swiftpaxos.md): its two error variables hold their `errors.New` errors for good (the lab's `replica.pkgSt`: `NewQuorumSystem` compares with them).
-/
module

public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.replica
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.encoding.binary.Link
public import Proof.encoding.json.Base
public import Perennial.Proof.errors.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Dsverify.Proof.bufio.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.config.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.dlog.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.rpc.Init
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.state.Init
public import Net.Proof.net.Init
public import Net.Proof.os.Init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.imdea_software.swiftpaxos.replica

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.replica :=
  define_is_pkg_init iprop(_root_.Perennial.errors.newVar replica.NO_QUORUM_FILE go!"Quorum file is not provided" ∗
      _root_.Perennial.errors.newVar replica.THREE_QUARTERS go!"ThreeQuarters")
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.replica :=
  build_get_is_pkg_init_wf

end def_

end github_com.imdea_software.swiftpaxos.replica
end Perennial

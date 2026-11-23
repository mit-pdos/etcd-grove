/-
The package fact of `gryff.src.gryff` (dsv-gryff, notes/dsv-gryff.md): `True`. Its mutable variables (`stack`, `cpMarker`, `cpcounter`, the counters, the message
buffers, `deferMap`) and the trace prophecy `traceProph` (ghost code, D13) are owned by the
replica node, not facts: a node gets them from its own boot (`Dsverify/Proof/gryff/Boot/Init.lean`,
notes/dsv-gryff.md, "Package initializers")
-/
module

public import Dsverify.GeneratedProof.gryff.src.gryff
public import Dsverify.Proof.gryff.src.epaxosproto.Init
public import Perennial.Proof.sort.Link
public import Perennial.Proof.time.Link
public import Dsverify.Proof.gryff.src.dlog.Init
public import Dsverify.Proof.gryff.src.gryffproto.Init
public import Dsverify.Proof.gryff.src.bloomfilter.Init
public import Perennial.Proof.encoding.binary.Link
public import Dsverify.Proof.gryff.src.fastrpc.Init
public import Dsverify.Proof.gryff.src.genericsmr.Init
public import Dsverify.Proof.gryff.src.genericsmrproto.Init
public import Perennial.Proof.io.Link
public import Perennial.Proof.log.Link
public import Perennial.Proof.math.Link
public import Dsverify.Proof.gryff.src.state.Init
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Dsverify.Proof.gryff.src.gryffcommon.Init
public import Dsverify.Proof.bufio.Init
public import Dsverify.Proof.gryff.src.clientproto.Init
public import Perennial.Proof.fmt.Link
public import Dsverify.Proof.math.rand.Init
public import Dsverify.Proof.gryff.src.stats.Init
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace gryff.src.gryff

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.gryff.src.gryff :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.gryff :=
  build_get_is_pkg_init_wf

end def_

end gryff.src.gryff
end Perennial

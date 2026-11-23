/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Slots.lean and the package-state part of
the lab's generated statement `GryffNetSpec.lean` (`GryffNetPkgState`, each package's `IsPkgInit`
instance from it) (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The packages' post-initialization predicates (`pkgStates`): `dlog`'s `DLOG` is `false` for good;
every other package's is `True`. Gryff's mutable package variables are owned by the replica (D3).
(The lab's `GryffNames` slot is `Names.lean`; the shares are `Shares.lean`.)
-/
module

public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.errors
public import Perennial.Proof.io
public import Perennial.Proof.log
public import Perennial.Proof.math
public import Perennial.Proof.sort
public import Perennial.Proof.sync
public import Perennial.Proof.encoding.binary
public import Perennial.Proof.strings
public import Perennial.Proof.strconv
public import Perennial.Proof.fmt
public import Perennial.Proof.time
public import Perennial.Proof.runtime
public import Proof.bufio.PkgInit
public import Net.Proof.net.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Base
public import Dsverify.Proof.gryff.Hyp.PkgInit

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

namespace gryff

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [libSt : hyp.LibPkgState GF]

/-- The run's choice of each package's own post-initialization predicate (`isPkgInitDef`:
its package-level state, e.g. `errors.newVar` for an `errors.New` variable); the test
package's is `True`. Not in the trust base: `SafeDist` does not mention it, and the run
proves each package's initialization establishes it. -/
class GryffNetPkgState (GF : BundledGFunctors) where
  /-- `gryff/src/fastrpc`'s package-level state -/
  fastrpc : IProp GF
  /-- `gryff/src/dlog`'s package-level state -/
  dlog : IProp GF
  /-- `gryff/src/state`'s package-level state -/
  state : IProp GF
  /-- `gryff/src/stats`'s package-level state -/
  stats : IProp GF
  /-- `gryff/src/clientproto`'s package-level state -/
  clientproto : IProp GF
  /-- `gryff/src/genericsmrproto`'s package-level state -/
  genericsmrproto : IProp GF
  /-- `gryff/src/masterproto`'s package-level state -/
  masterproto : IProp GF
  /-- `gryff/src/epaxosproto`'s package-level state -/
  epaxosproto : IProp GF
  /-- `gryff/src/gryffproto`'s package-level state -/
  gryffproto : IProp GF
  /-- `gryff/src/bitvec`'s package-level state -/
  bitvec : IProp GF
  /-- `gryff/src/bloomfilter`'s package-level state -/
  bloomfilter : IProp GF
  /-- `gryff/src/genericsmr`'s package-level state -/
  genericsmr : IProp GF
  /-- `gryff/src/gryffcommon`'s package-level state -/
  gryffcommon : IProp GF
  /-- `gryff/src/gryff`'s package-level state -/
  gryff : IProp GF
  /-- `gryff/src/masterlib`'s package-level state -/
  masterlib : IProp GF
  /-- `gryff/src/serverlib`'s package-level state -/
  serverlib : IProp GF

/-- A choice of `GryffNetPkgState` at every heap. -/
abbrev GryffNetPkgStates [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] :=
  ∀ {GF : BundledGFunctors} [HeapGS HasLC.hasLC GF] [go.Semantics], GryffNetPkgState GF

instance fastrpc_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.fastrpc :=
  define_is_pkg_init (pkgState.fastrpc)
instance fastrpc_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.fastrpc :=
  build_get_is_pkg_init_wf

instance dlog_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.dlog :=
  define_is_pkg_init (pkgState.dlog)
instance dlog_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.dlog :=
  build_get_is_pkg_init_wf

instance state_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.state :=
  define_is_pkg_init (pkgState.state)
instance state_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.state :=
  build_get_is_pkg_init_wf

instance stats_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.stats :=
  define_is_pkg_init (pkgState.stats)
instance stats_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.stats :=
  build_get_is_pkg_init_wf

instance clientproto_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.clientproto :=
  define_is_pkg_init (pkgState.clientproto)
instance clientproto_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.clientproto :=
  build_get_is_pkg_init_wf

instance genericsmrproto_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.genericsmrproto :=
  define_is_pkg_init (pkgState.genericsmrproto)
instance genericsmrproto_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.genericsmrproto :=
  build_get_is_pkg_init_wf

instance masterproto_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.masterproto :=
  define_is_pkg_init (pkgState.masterproto)
instance masterproto_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.masterproto :=
  build_get_is_pkg_init_wf

instance epaxosproto_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.epaxosproto :=
  define_is_pkg_init (pkgState.epaxosproto)
instance epaxosproto_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.epaxosproto :=
  build_get_is_pkg_init_wf

instance gryffproto_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.gryffproto :=
  define_is_pkg_init (pkgState.gryffproto)
instance gryffproto_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.gryffproto :=
  build_get_is_pkg_init_wf

instance bitvec_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.bitvec :=
  define_is_pkg_init (pkgState.bitvec)
instance bitvec_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.bitvec :=
  build_get_is_pkg_init_wf

instance bloomfilter_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.bloomfilter :=
  define_is_pkg_init (pkgState.bloomfilter)
instance bloomfilter_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.bloomfilter :=
  build_get_is_pkg_init_wf

instance genericsmr_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.genericsmr :=
  define_is_pkg_init (pkgState.genericsmr)
instance genericsmr_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.genericsmr :=
  build_get_is_pkg_init_wf

instance gryffcommon_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.gryffcommon :=
  define_is_pkg_init (pkgState.gryffcommon)
instance gryffcommon_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.gryffcommon :=
  build_get_is_pkg_init_wf

instance gryff_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.gryff :=
  define_is_pkg_init (pkgState.gryff)
instance gryff_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.gryff :=
  build_get_is_pkg_init_wf

instance masterlib_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.masterlib :=
  define_is_pkg_init (pkgState.masterlib)
instance masterlib_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.masterlib :=
  build_get_is_pkg_init_wf

instance serverlib_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.src.serverlib :=
  define_is_pkg_init (pkgState.serverlib)
instance serverlib_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.src.serverlib :=
  build_get_is_pkg_init_wf

instance gryffnet_isPkgInit_inst [pkgState : GryffNetPkgState GF] :
    IsPkgInit (IProp GF) pkg_id.gryff.examples.gryffnet :=
  define_is_pkg_init iprop(True)
instance gryffnet_get_isPkgInit_wf_inst [pkgState : GryffNetPkgState GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.gryff.examples.gryffnet :=
  build_get_is_pkg_init_wf

end defs

/-- The packages' post-initialization predicates: `dlog`'s `DLOG` is `false` for good (no
code writes it after initialization); every other package's is `True` (no package-level state
a proof reads through `isPkgInit`). Gryff's mutable package variables are owned by the replica
(D3). -/
def pkgStates [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] : GryffNetPkgStates := fun {_GF} [_] [_] =>
  { fastrpc := iprop(True),
    dlog := iprop(globalAddr _root_.Perennial.gryff.src.dlog.DLOG ↦□ false), state := iprop(True), stats := iprop(True),
    clientproto := iprop(True), genericsmrproto := iprop(True), masterproto := iprop(True),
    epaxosproto := iprop(True), gryffproto := iprop(True), bitvec := iprop(True),
    bloomfilter := iprop(True), genericsmr := iprop(True), gryffcommon := iprop(True),
    gryff := iprop(True), masterlib := iprop(True), serverlib := iprop(True) }

/-- The packages' state as an instance (what `kit_isPkgInit` resolves to). -/
instance pkgStateInst [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] {GF : BundledGFunctors} [HeapGS HasLC.hasLC GF]
    [go.Semantics] : GryffNetPkgState GF := pkgStates

end gryff

end Perennial

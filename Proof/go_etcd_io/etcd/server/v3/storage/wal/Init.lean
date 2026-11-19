/-
Package initialization of `go_etcd_io.etcd.server.v3.storage.wal`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`walInit`, `PkgInit.lean`): `crcTable` holds the Castagnoli table (`walCrcTable`), the
metrics `walFsyncSec`, `walWriteSec` (histograms) and `walWriteBytes` (a gauge) hold metrics whose
`Observe`/`Add` return (`wal.metricsInit`), `SegmentSizeBytes` holds `64000000`, every error
variable an error whose `Error()` returns and on which `errors.Is` returns (`wal.errVar`), and `openWALFilesFn` the function
`openWALFiles`, read-only for good. Its initializer
allocates its variables, initializes its imports and runs their initializers: the metrics'
untranslated `prometheus` constructors (the trust-boundary axioms `<X>_init`, metrics.go), the
translated `errors.New` calls, `ErrCRCMismatch = walpb.ErrCRCMismatch` (`walpbInit`), `crcTable =
crc32.MakeTable(crc32.Castagnoli)` (`hash.crc32.MakeTable.wp_proof`), and its untranslated `init`
function (`prometheus.MustRegister` of the metrics), which the trust-boundary axiom `initFuncsOk`
says returns.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.Init
public import Proof.go_etcd_io.etcd.pkg.v3.crc.Init
public import Proof.go_etcd_io.etcd.pkg.v3.ioutil.Init
public import Proof.go_etcd_io.etcd.pkg.v3.pbutil.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_uber_org.zap.Init
public import Proof.hash.Init
public import Proof.hash.crc32.Init
public import Proof.os.Init
public import Proof.path.filepath.Init
public import Perennial.Proof.errors.NewVar
public import Proof.errors.ErrIsTerm
public import Proof.errors.ErrorStringOk

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace go_etcd_io.etcd.server.v3.storage.wal
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.storage.wal`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `walFsyncSec = prometheus.New...(...)` (`metrics.go`): a metric whose method returns. -/
axiom walFsyncSec_init :
    {{ (True : IProp GF) }} (App (Val walFsyncSec.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr walFsyncSec ↦ GoInterface.ok h ∗ EtcdGrove.wal.histSpec h }}

/-- `walWriteSec = prometheus.New...(...)` (`metrics.go`): a metric whose method returns. -/
axiom walWriteSec_init :
    {{ (True : IProp GF) }} (App (Val walWriteSec.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr walWriteSec ↦ GoInterface.ok h ∗ EtcdGrove.wal.histSpec h }}

/-- `walWriteBytes = prometheus.New...(...)` (`metrics.go`): a metric whose method returns. -/
axiom walWriteBytes_init :
    {{ (True : IProp GF) }} (App (Val walWriteBytes.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr walWriteBytes ↦ GoInterface.ok h ∗ EtcdGrove.wal.gaugeAddSpec h }}

end go_etcd_io.etcd.server.v3.storage.wal
end opaqueInits

end Perennial

/-
Package initialization of `go_etcd_io.etcd.server.v3.storage.wal`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`walInit`, `PkgInit.lean`): `crcTable` holds the Castagnoli table (`walCrcTable`), the
metrics `walFsyncSec`, `walWriteSec` (histograms) and `walWriteBytes` (a gauge) hold metrics whose
`Observe`/`Add` return (`wal.metricsInit`), `SegmentSizeBytes` holds `64000000`, `MaxSaveBatchBytes`
`2^42` (fix 0009), every error
variable an error whose `Error()` returns and on which `errors.Is` returns (`wal.errVar`), and `openWALFilesFn` the function
`openWALFiles`, read-only for good. Its initializer
allocates its variables, initializes its imports and runs their initializers: the metrics'
translated `prometheus` constructors (metrics.go, over prometheus's `NewHistogram`, `ExponentialBuckets`
and `NewGauge` specs; until 2026-11-19 the trust-boundary axioms `<X>_init`), the
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
public import Proof.github_com.prometheus.client_golang.prometheus.MetricLaws
public import Proof.github_com.prometheus.client_golang.prometheus.Registry
public import Proof.runtime.PkgInitRes

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

namespace go_etcd_io.etcd.server.v3.storage.wal

/-- The fully-qualified names of the metrics this package's `init()` registers with
prometheus's default registry, in its order (`MustRegister`; `metrics.go`). -/
def regNames : List GoString :=
  [EtcdGrove.prometheus.fqName go!"etcd" go!"disk" go!"wal_fsync_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd" go!"disk" go!"wal_write_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd" go!"disk" go!"wal_write_bytes_total"]

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names: their registration rights are its initializer's
resources (`ownInitResL`, `Proof/runtime/PkgInitRes.lean`). -/
def regQs : List (GoString × List GoString) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.storage.wal, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal.regNames)]

/-- The metric names its initializer registers, with those of its import closure: its
`wp_initialize'`'s precondition has the rights to register them (`namesFree`). -/
def initNames : List GoString := regQs.flatMap (·.2)

end go_etcd_io.etcd.server.v3.storage.wal

end Perennial

/-
Package initialization of `go_etcd_io.etcd.server.v3.storage.backend`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`backendInit`, `Base.lean`): the commit's histograms `rebalanceSec`,
`spillSec`, `writeSec`, `commitSec` hold `Histogram`s whose `Observe` returns, and `boltOpenOptions` (`boltOpenOptionsOk`), and `defaultBatchInterval`,
`defaultBatchLimit`, `InitialMmapSize` their translated initializers' constants. Its initializer
allocates and sets its translated constants, initializes its imports and runs its variables'
untranslated initializers: the four the fact reads are translated (`metrics.go`:
`prometheus.NewHistogram(...)` of `ExponentialBuckets`, over their specs; until 2026-11-19 the
trust-boundary axioms `<X>_init`), and so are (2026-11-19, until then `opaqueInitsOk`) the others,
`defragSec`, `defragBlockingSec` and the gauge `isDefragActive`; (2026-11-21) `snapshotTransferSec`'s
histogram, which `Snapshot`'s goroutine observes, is in the fact, and so is `minSnapshotWarningTimeout`,
the floor of its ticker's interval.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.encoding.hex.Init
public import Proof.github_com.dustin.go_humanize.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.bbolt.errors.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Init
public import Proof.go_uber_org.zap.Init
public import Proof.syscall.Init
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

namespace go_etcd_io.etcd.server.v3.storage.backend

/-- The fully-qualified names of the metrics this package's `init()` registers with
prometheus's default registry, in its order (`MustRegister`; `metrics.go`). -/
def regNames : List GoString :=
  [EtcdGrove.prometheus.fqName go!"etcd" go!"disk" go!"backend_commit_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"disk" go!"backend_commit_rebalance_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"disk" go!"backend_commit_spill_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd_debugging" go!"disk" go!"backend_commit_write_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd" go!"disk" go!"backend_defrag_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd" go!"disk" go!"backend_defrag_blocking_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd" go!"disk" go!"backend_snapshot_duration_seconds",
   EtcdGrove.prometheus.fqName go!"etcd" go!"disk" go!"defrag_inflight"]

/-- The IDs besides its names' this package's initializer takes the rights to (prom-registry:
a later registration's, `REG_KEYS`). -/
def regKeys : List w64 := []

/-- The packages of this package's import closure (itself included) whose initializers
register metrics, with their names and other IDs: their registration rights are its
initializer's resources (`ownInitResL`, `Proof/runtime/PkgInitRes.lean`; its `wp_initialize'`'s
precondition: `regsFree regQs`). -/
def regQs : List (GoString × List GoString × List w64) :=
  [(pkg_id.go_etcd_io.etcd.server.v3.storage.backend, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regNames, _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.regKeys)]

end go_etcd_io.etcd.server.v3.storage.backend

end Perennial

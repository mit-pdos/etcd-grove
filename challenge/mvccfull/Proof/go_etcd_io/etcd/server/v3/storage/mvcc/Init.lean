/-
Package initialization of `go_etcd_io.etcd.server.v3.storage.mvcc`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`mvccInit`, `Base.lean`): its error variables (translated `errors.New` calls), its
metrics (`metrics.go`, untranslated: the trust-boundary axioms `<X>_init`; a counter's `Add` only
of a non-negative value), its constants, and `schema`'s two compaction key names (from `schema`'s
fact). `opaqueInitsOk` states its other untranslated initializers run.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.context.Link
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.dustin.go_humanize.Init
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.PkgInit
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Pkg
public import Code.go_etcd_io.raft.v3
public import Code.go_etcd_io.raft.v3.confchange
public import Code.go_etcd_io.raft.v3.raftpb
public import Code.go_etcd_io.raft.v3.tracker
public import Code.google_golang_org.protobuf.proto
public import Code.k8s_io.utils.third_party.forked.golang.btree
public import Perennial.Code.bytes
public import Perennial.Code.cmp
public import Perennial.Code.context
public import Perennial.Code.encoding.binary
public import Perennial.Code.errors
public import Perennial.Code.fmt
public import Perennial.Code.github_com.goose_lang.primitive
public import Perennial.Code.internal.oserror
public import Perennial.Code.internal.stringslite
public import Perennial.Code.io
public import Perennial.Code.iter
public import Perennial.Code.log
public import Perennial.Code.math
public import Perennial.Code.slices
public import Perennial.Code.sort
public import Perennial.Code.strconv
public import Perennial.Code.strings
public import Perennial.Code.sync
public import Perennial.Code.sync.atomic
public import Perennial.Code.time
public import Perennial.Code.«unsafe»
public import Proof.go_etcd_io.etcd.client.v3.Init
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.strings.Link
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.sync.Link
public import Proof.go_uber_org.zap.Init
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.schema.Init
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strconv.Base
public import Proof.reflect.PkgInit
public import Perennial.GeneratedProof.bytes
public import Perennial.GeneratedProof.context
public import Perennial.GeneratedProof.crypto.rand
public import Perennial.GeneratedProof.encoding.binary
public import Perennial.GeneratedProof.errors
public import Perennial.GeneratedProof.fmt
public import Perennial.GeneratedProof.cmp
public import Perennial.GeneratedProof.math
public import Perennial.GeneratedProof.slices
public import Perennial.GeneratedProof.strconv
public import Perennial.GeneratedProof.strings
public import Perennial.Golang.Theory
public import Code.go_etcd_io.raft.v3.quorum
public import GeneratedProof.google_golang_org.protobuf.internal.pragma
public import Code.google_golang_org.protobuf.reflect.protoreflect
public import GeneratedProof.google_golang_org.protobuf.internal.impl
public import Code.google_golang_org.protobuf.runtime.protoimpl
public import GeneratedProof.go_etcd_io.raft.v3.tracker
public import Perennial.GeneratedProof.io
public import Perennial.GeneratedProof.log
public import Perennial.GeneratedProof.math.big
public import GooseLang.Ext.Fs.Impl
public import Perennial.GeneratedProof.sync
public import Code.syscall
public import Code.internal.syscall.unix
public import Code.internal.poll
public import Perennial.GeneratedProof.internal.oserror
public import Perennial.GeneratedProof.time
public import Code.io.fs
public import Code.os
public import GeneratedProof.go_etcd_io.raft.v3.chunk2
public import Perennial.Code.reflect
public import Perennial.Proof.context
public import Perennial.Proof.sync
public import Perennial.Proof.fmt
public import Perennial.Proof.slices
public import Perennial.Proof.cmp
public import Proof.errors.NewVar
public import Perennial.Proof.encoding.binary
public import Perennial.Proof.strings
public import Perennial.Proof.math
public import Perennial.Proof.math.bits
public import Perennial.Proof.crypto.rand
public import Perennial.Proof.bytes
public import Perennial.Proof.log
public import Perennial.Proof.io
public import Perennial.Proof.errors
public import Proof.os.PkgInit
public import Perennial.Proof.context.NewErrorString
public import Perennial.Proof.errors.Link
public import Perennial.Proof.io.Link
public import Proof.internal.poll.PkgInit
public import Proof.internal.syscall.unix.PkgInit
public import Proof.syscall.PkgInit
public import Perennial.Proof.fmt.SprintfModel
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.internal.oserror.Link
public import Perennial.Proof.time.Link
public import Spec.fmt.ErrorOk
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.go_opentelemetry_io.otel.trace.Init
public import Proof.go_uber_org.zap.Init
public import Proof.hash.PkgInit
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init
public import Perennial.Proof.context.NewErrorString
public import Perennial.Proof.errors.NewVar
public import Proof.errors.NewVarCell
public import Perennial.Proof.sync.RWMutexGuard

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
namespace go_etcd_io.etcd.server.v3.storage.mvcc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.storage.mvcc`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([totalEventsCounter.init,
        dbTotalSize.init,
        dbTotalSizeInUse.init,
        dbOpenReadTxN.init,
        hashSec.init,
        hashRevSec.init,
        currentRev.init,
        compactRev.init,
        «_».init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.storage.mvcc`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `rangeCounter = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`: `Inc` returns, and `Add` of a non-negative value. -/
axiom rangeCounter_init :
    {{ (True : IProp GF) }} (App (Val rangeCounter.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr rangeCounter ↦ GoInterface.ok m ∗ counterSpec m }}

/-- `putCounter = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`: `Inc` returns, and `Add` of a non-negative value. -/
axiom putCounter_init :
    {{ (True : IProp GF) }} (App (Val putCounter.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr putCounter ↦ GoInterface.ok m ∗ counterSpec m }}

/-- `deleteCounter = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`: `Inc` returns, and `Add` of a non-negative value. -/
axiom deleteCounter_init :
    {{ (True : IProp GF) }} (App (Val deleteCounter.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr deleteCounter ↦ GoInterface.ok m ∗ counterSpec m }}

/-- `txnCounter = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`: `Inc` returns, and `Add` of a non-negative value. -/
axiom txnCounter_init :
    {{ (True : IProp GF) }} (App (Val txnCounter.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr txnCounter ↦ GoInterface.ok m ∗ counterSpec m }}

/-- `dbCompactionKeysCounter = prometheus.NewCounter(...)` (`metrics.go`): a `Counter`: `Inc` returns, and `Add` of a non-negative value. -/
axiom dbCompactionKeysCounter_init :
    {{ (True : IProp GF) }} (App (Val dbCompactionKeysCounter.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr dbCompactionKeysCounter ↦ GoInterface.ok m ∗ counterSpec m }}

/-- `watchStreamGauge = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom watchStreamGauge_init :
    {{ (True : IProp GF) }} (App (Val watchStreamGauge.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr watchStreamGauge ↦ GoInterface.ok m ∗ gaugeSpec m }}

/-- `watcherGauge = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom watcherGauge_init :
    {{ (True : IProp GF) }} (App (Val watcherGauge.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr watcherGauge ↦ GoInterface.ok m ∗ gaugeSpec m }}

/-- `pendingEventsGauge = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom pendingEventsGauge_init :
    {{ (True : IProp GF) }} (App (Val pendingEventsGauge.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr pendingEventsGauge ↦ GoInterface.ok m ∗ gaugeSpec m }}

/-- `totalPutSizeGauge = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom totalPutSizeGauge_init :
    {{ (True : IProp GF) }} (App (Val totalPutSizeGauge.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr totalPutSizeGauge ↦ GoInterface.ok m ∗ gaugeSpec m }}

/-- `slowWatcherGauge = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom slowWatcherGauge_init :
    {{ (True : IProp GF) }} (App (Val slowWatcherGauge.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr slowWatcherGauge ↦ GoInterface.ok m ∗ gaugeSpec m ∗ gaugeSetSpec m }}

/-- `keysGauge = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom keysGauge_init :
    {{ (True : IProp GF) }} (App (Val keysGauge.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr keysGauge ↦ GoInterface.ok m ∗ gaugeSpec m ∗ gaugeSetSpec m }}

/-- `dbCompactionLast = prometheus.NewGauge(...)` (`metrics.go`): a `Gauge`, whose `Inc`, `Dec`, `Add`, `Set` return. -/
axiom dbCompactionLast_init :
    {{ (True : IProp GF) }} (App (Val dbCompactionLast.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr dbCompactionLast ↦ GoInterface.ok m ∗ gaugeSetSpec m }}

/-- `indexCompactionPauseMs = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom indexCompactionPauseMs_init :
    {{ (True : IProp GF) }} (App (Val indexCompactionPauseMs.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr indexCompactionPauseMs ↦ GoInterface.ok m ∗ histSpec m }}

/-- `dbCompactionPauseMs = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom dbCompactionPauseMs_init :
    {{ (True : IProp GF) }} (App (Val dbCompactionPauseMs.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr dbCompactionPauseMs ↦ GoInterface.ok m ∗ histSpec m }}

/-- `dbCompactionTotalMs = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom dbCompactionTotalMs_init :
    {{ (True : IProp GF) }} (App (Val dbCompactionTotalMs.init) (Val #()))
    {{ RET #(); ∃ m : GoInterfaceOk, globalAddr dbCompactionTotalMs ↦ GoInterface.ok m ∗ histSpec m }}

/-- `defaultCompactionBatchLimit = 1000` (`kvstore.go`). -/
axiom defaultCompactionBatchLimit_init :
    {{ (True : IProp GF) }} (App (Val defaultCompactionBatchLimit.init) (Val #()))
    {{ RET #(); globalAddr defaultCompactionBatchLimit ↦ (W64 1000 : w64) }}

/-- `defaultCompactionSleepInterval = 10 * time.Millisecond` (`kvstore.go`). -/
axiom defaultCompactionSleepInterval_init :
    {{ (True : IProp GF) }} (App (Val defaultCompactionSleepInterval.init) (Val #()))
    {{ RET #(); ∃ d : w64, globalAddr defaultCompactionSleepInterval ↦ d }}

end go_etcd_io.etcd.server.v3.storage.mvcc
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [_root_.Perennial.errors.Assumptions]

namespace go_etcd_io.etcd.server.v3.storage.mvcc

end go_etcd_io.etcd.server.v3.storage.mvcc

end init

end Perennial

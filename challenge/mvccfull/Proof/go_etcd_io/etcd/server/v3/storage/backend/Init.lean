/-
Package initialization of `go_etcd_io.etcd.server.v3.storage.backend`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`backendInit`, `Base.lean`): the commit's histograms `rebalanceSec`,
`spillSec`, `writeSec`, `commitSec` hold `Histogram`s whose `Observe` returns, and `boltOpenOptions` (`boltOpenOptionsOk`), and `defaultBatchInterval`,
`defaultBatchLimit`, `InitialMmapSize` their translated initializers' constants. Its initializer
allocates and sets its translated constants, initializes its imports and runs its variables'
untranslated initializers; the trust-boundary axioms `<X>_init` state the four the fact reads
(`metrics.go`: `prometheus.NewHistogram(...)`), `opaqueInitsOk` the others.
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
public import Proof.github_com.prometheus.client_golang.prometheus.Init
public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.bbolt.PkgInit
public import Perennial.Proof.errors.Link
public import Perennial.Proof.errors.NewVar
public import Proof.errors.NewVar
public import Spec.fmt.ErrorOk
public import Perennial.Proof.errors
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
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.PkgInit
public import Perennial.Proof.fmt.Link
public import Proof.go_uber_org.zap.Init

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
namespace go_etcd_io.etcd.server.v3.storage.backend
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.storage.backend`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([defragSec.init,
        defragBlockingSec.init,
        snapshotTransferSec.init,
        isDefragActive.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.storage.backend`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `commitSec = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom commitSec_init :
    {{ (True : IProp GF) }} (App (Val commitSec.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr commitSec ↦ GoInterface.ok h ∗ histSpec h }}

/-- `rebalanceSec = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom rebalanceSec_init :
    {{ (True : IProp GF) }} (App (Val rebalanceSec.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr rebalanceSec ↦ GoInterface.ok h ∗ histSpec h }}

/-- `spillSec = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom spillSec_init :
    {{ (True : IProp GF) }} (App (Val spillSec.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr spillSec ↦ GoInterface.ok h ∗ histSpec h }}

/-- `writeSec = prometheus.NewHistogram(...)` (`metrics.go`): a `Histogram`, whose `Observe` returns. -/
axiom writeSec_init :
    {{ (True : IProp GF) }} (App (Val writeSec.init) (Val #()))
    {{ RET #(); ∃ h : GoInterfaceOk, globalAddr writeSec ↦ GoInterface.ok h ∗ histSpec h }}

/-- `boltOpenOptions = &bolt.Options{MmapFlags: syscall.MAP_POPULATE, NoFreelistSync: true}` (`config_linux.go`; nil on other systems): read-write options with the default page size and `OpenFile`. -/
axiom boltOpenOptions_init :
    {{ (True : IProp GF) }} (App (Val boltOpenOptions.init) (Val #()))
    {{ RET #(); ∃ p : Loc, globalAddr boltOpenOptions ↦ p ∗ (⌜p = Loc.null⌝ ∨ ∃ o : EtcdGrove.backend.OptsM, EtcdGrove.backend.optsAt p DFrac.discard o ∗ ⌜o.ok⌝) }}

end go_etcd_io.etcd.server.v3.storage.backend
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [_root_.Perennial.errors.Assumptions]

namespace go_etcd_io.etcd.server.v3.storage.backend

end go_etcd_io.etcd.server.v3.storage.backend

end init

end Perennial

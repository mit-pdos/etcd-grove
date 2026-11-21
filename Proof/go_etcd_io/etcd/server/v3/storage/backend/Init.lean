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
histogram, which `Snapshot`'s goroutine observes, is in the fact.
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

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.storage.backend`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `boltOpenOptions = &bolt.Options{MmapFlags: syscall.MAP_POPULATE, NoFreelistSync: true}` (`config_linux.go`; nil on other systems, but the file model is Linux's, configuration C): read-write options with the default page size and `OpenFile`, `NoFreelistSync`, no `Timeout`. (S3e, 2026-11-18: until then possibly nil.) -/
axiom boltOpenOptions_init :
    {{ (True : IProp GF) }} (App (Val boltOpenOptions.init) (Val #()))
    {{ RET #(); ∃ p : Loc, globalAddr boltOpenOptions ↦ p ∗ ∃ o : EtcdGrove.backend.OptsM, EtcdGrove.backend.optsAt p DFrac.discard o ∗ ⌜o.ok ∧ o.noFreelistSync = true ∧ o.timeout = W64 0⌝ }}

end go_etcd_io.etcd.server.v3.storage.backend
end opaqueInits

end Perennial

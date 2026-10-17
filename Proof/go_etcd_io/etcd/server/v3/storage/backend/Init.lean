/-
Package initialization of `go_etcd_io.etcd.server.v3.storage.backend`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`backendInit`, `Base.lean`): the commit's histograms `rebalanceSec`,
`spillSec`, `writeSec`, `commitSec` hold `Histogram`s whose `Observe` returns. Its initializer
allocates and sets its translated constants, initializes its imports and runs its variables'
untranslated initializers; the trust-boundary axioms `<X>_init` state the four the fact reads
(`metrics.go`: `prometheus.NewHistogram(...)`), `opaqueInitsOk` the others.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.math.Link
public import Perennial.Proof.sort.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.encoding.hex.Init
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.storage.backend`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([boltOpenOptions.init,
        defragSec.init,
        defragBlockingSec.init,
        snapshotTransferSec.init,
        isDefragActive.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

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

end go_etcd_io.etcd.server.v3.storage.backend
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [EtcdGrove.ErrorStringLeaf]

namespace go_etcd_io.etcd.server.v3.storage.backend

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.storage.backend get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := w64) minSnapshotWarningTimeout _ as HminSnapshotWarningTimeout
  wp_apply wp_GlobalAlloc (V := w64) InitialMmapSize _ as HInitialMmapSize
  wp_apply wp_GlobalAlloc (V := w64) defragLimit _ as HdefragLimit
  wp_apply wp_GlobalAlloc (V := w64) defaultBatchInterval _ as HdefaultBatchInterval
  wp_apply wp_GlobalAlloc (V := w64) defaultBatchLimit _ as HdefaultBatchLimit
  wp_apply _root_.Perennial.sort.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply _root_.Perennial.encoding.hex.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply _root_.Perennial.github_com.prometheus.client_golang.prometheus.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply _root_.Perennial.go_etcd_io.bbolt.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply _root_.Perennial.math.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.client.pkg.v3.verify.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply _root_.Perennial.go_etcd_io.bbolt.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply _root_.Perennial.go_uber_org.zap.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply _root_.Perennial.bytes.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of defaultBatchLimit))
  -- translated initializer of defaultBatchInterval))
  -- translated initializer of defragLimit))
  -- translated initializer of InitialMmapSize))
  -- translated initializer of minSnapshotWarningTimeout))
  wp_apply (opaqueInitsOk boltOpenOptions.init (by mem_tac))
  wp_apply commitSec_init as ⟨%hcommitSec, HcommitSec, #ScommitSec⟩
  wp_apply rebalanceSec_init as ⟨%hrebalanceSec, HrebalanceSec, #SrebalanceSec⟩
  wp_apply spillSec_init as ⟨%hspillSec, HspillSec, #SspillSec⟩
  wp_apply writeSec_init as ⟨%hwriteSec, HwriteSec, #SwriteSec⟩
  wp_apply (opaqueInitsOk defragSec.init (by mem_tac))
  wp_apply (opaqueInitsOk defragBlockingSec.init (by mem_tac))
  wp_apply (opaqueInitsOk snapshotTransferSec.init (by mem_tac))
  wp_apply (opaqueInitsOk isDefragActive.init (by mem_tac))
  ipersist HcommitSec
  ipersist HrebalanceSec
  ipersist HspillSec
  ipersist HwriteSec
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold backendInit
  iframe #


end go_etcd_io.etcd.server.v3.storage.backend

end init

end Perennial

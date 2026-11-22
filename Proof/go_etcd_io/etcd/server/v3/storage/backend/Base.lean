/-
Package initialization instances for etcd's backend (`server/v3/storage/backend`, translated
with bodies: `Code/go_etcd_io/etcd/server/v3/storage/backend.toml`) and the packages it imports
that no lower proof module provides (bbolt's and `encoding/hex`'s are
`Proof/go_etcd_io/bbolt/PkgInit.lean`):
`client/pkg/v3/verify` and prometheus's `client_golang/prometheus` (names only). The others are
the cache's (`cache/v3/Base.lean`: `zap`) and Perennial's (`bytes`, `errors`, `fmt`, `math`,
`sort`, `sync`, `sync/atomic`, `time`).

2026-10-12: moved here from `etcdserver/Base.lean` (backend, verify), `etcdserver/BaseApply.lean`
(bbolt) and mvcc's `Base.lean` (prometheus), unchanged, when the backend got bodies: its
instance's well-formedness needs those of every package it imports.

As in those, the package facts are assumptions about package initialization, not proved from
`initialize'`; they are `True`, but for bbolt's `errors` (`bboltErrorsInit`: `ErrBucketNotFound`,
an `errors.New` error) and the backend's (`backendInit`: the commit's prometheus histograms, and
its defaults),
2026-10-12, the backend's unit 2.
-/
module

public import Code.go_etcd_io.etcd.server.v3.storage.backend
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.backend
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.bytes
public import Perennial.Proof.errors
public import Perennial.Proof.fmt
public import Perennial.Proof.math
public import Perennial.Proof.sort
public import Perennial.Proof.sync
public import Perennial.Proof.sync.atomic
public import Perennial.Proof.time
public import Proof.go_etcd_io.bbolt.PkgInit
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BboltOptsDefs
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.PkgInit
public import Proof.github_com.prometheus.client_golang.prometheus.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

-- (`encoding/hex`'s, bbolt's and bbolt `errors`' instances, `bboltErrorsInit`:
-- `Proof/go_etcd_io/bbolt/PkgInit.lean`)



-- (S4b, 2026-11-18: moved here from mvcc's `Base.lean`, the snapshot's goroutine calls
-- `humanize.Bytes`)
namespace github_com.dustin.go_humanize

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.dustin.go_humanize :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.dustin.go_humanize :=
  build_get_is_pkg_init_wf

end github_com.dustin.go_humanize

namespace go_etcd_io.etcd.server.v3.storage.backend

/-- A prometheus `Histogram` as the backend uses it: `Observe(x)` returns (metrics have no effect
the model sees). -/
def histSpec (h : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ x : w64, {{ True }} (App (Val #(methods h.ty go!"Observe" h.v)) (Val #x))
    {{ RET #(); True }}))

instance histSpec_persistent (h : GoInterfaceOk) : Persistent (histSpec (GF := GF) h) := by
  unfold histSpec; infer_instance

/-- The backend's package facts: the commit's histograms of `metrics.go` (`rebalanceSec`,
`spillSec`, `writeSec`, `commitSec`), each a fixed interface value whose `Observe` returns; and
(item 8, 2026-10-17: until then a premise of `New`) `boltOpenOptions` (`boltOpenOptionsOk`); and
(2026-11-07, for `DefaultBackendConfig`'s loads) the defaults of `backend.go`, which nothing writes
after the initializer: `defaultBatchInterval = 100 * time.Millisecond`, `defaultBatchLimit = 10000`,
`InitialMmapSize = 10 * 1024 * 1024 * 1024`; (2026-11-21) the histogram `snapshotTransferSec` and
`minSnapshotWarningTimeout = 30 * time.Second` (`Snapshot`'s goroutine's). -/
abbrev backendInit : IProp GF :=
  iprop((∃ h : GoInterfaceOk, globalAddr rebalanceSec ↦□ GoInterface.ok h ∗ histSpec h) ∗
    (∃ h : GoInterfaceOk, globalAddr spillSec ↦□ GoInterface.ok h ∗ histSpec h) ∗
    (∃ h : GoInterfaceOk, globalAddr writeSec ↦□ GoInterface.ok h ∗ histSpec h) ∗
    (∃ h : GoInterfaceOk, globalAddr commitSec ↦□ GoInterface.ok h ∗ histSpec h) ∗
    EtcdGrove.backend.boltOpenOptionsOk ∗
    globalAddr defaultBatchInterval ↦□ (W64 100000000) ∗
    globalAddr defaultBatchLimit ↦□ (W64 10000) ∗
    globalAddr InitialMmapSize ↦□ (W64 10737418240) ∗
    -- (backend-snapshot B4, 2026-11-21) `snapshotTransferSec`, which `Snapshot`'s goroutine observes
    (∃ h : GoInterfaceOk, globalAddr snapshotTransferSec ↦□ GoInterface.ok h ∗ histSpec h) ∗
    -- (backend-snapshot B4, 2026-11-21) `minSnapshotWarningTimeout = 30 * time.Second`, which only the
    -- initializer writes (a `var` for etcd's tests): the floor of `Snapshot`'s ticker interval
    globalAddr minSnapshotWarningTimeout ↦□ (W64 30000000000))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend :=
  define_is_pkg_init backendInit
instance get_isPkgInit_wf_inst [EtcdGrove.prometheus.PromRegGS GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage.backend

end init

end Perennial

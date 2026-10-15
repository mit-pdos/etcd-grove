/-
Package initialization instances for etcd's backend (`server/v3/storage/backend`, translated
with bodies: `Code/go_etcd_io/etcd/server/v3/storage/backend.toml`) and the packages it imports
that no lower proof module provides: bbolt and its `errors` (names and types only; bbolt imports `time` and its `internal/common`, whose instance is `Proof/go_etcd_io/bbolt/internal/common/Init.lean`), `encoding/hex`
(a standard-library package Perennial does not translate: names only, here),
`client/pkg/v3/verify` and prometheus's `client_golang/prometheus` (names only). The others are
the cache's (`cache/v3/Base.lean`: `zap`) and Perennial's (`bytes`, `errors`, `fmt`, `math`,
`sort`, `sync`, `sync/atomic`, `time`).

2026-10-12: moved here from `etcdserver/Base.lean` (backend, verify), `etcdserver/BaseApply.lean`
(bbolt) and mvcc's `Base.lean` (prometheus), unchanged, when the backend got bodies: its
instance's well-formedness needs those of every package it imports.

As in those, the package facts are assumptions about package initialization, not proved from
`initialize'`; they are `True`, but for bbolt's `errors` (`bboltErrorsInit`: `ErrBucketNotFound`,
an `errors.New` error) and the backend's (`backendInit`: the commit's prometheus histograms),
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
public import Proof.go_etcd_io.bbolt.internal.common.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace encoding.hex

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.encoding.hex :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.encoding.hex :=
  build_get_is_pkg_init_wf

end encoding.hex

namespace go_etcd_io.bbolt

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.bbolt :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.bbolt :=
  build_get_is_pkg_init_wf

end go_etcd_io.bbolt

namespace go_etcd_io.bbolt.errors

/-- bbolt's `errors` package facts: `ErrBucketNotFound` (`errors.New("bucket not found")`, which
`DeleteBucket` returns and the backend compares with `errors.Is`) is a fixed `errors.New` error: a
pointer error, a leaf of an error tree, with no `Is` method (`*errorString` has only `Error`;
the model's method sets are uninterpreted, so this is stated, as `apply`'s `errLeaf`). -/
abbrev bboltErrorsInit : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr ErrBucketNotFound ↦□ GoInterface.ok e ∗
    ⌜_root_.Perennial.errors.IsPointerError e ∧ _root_.Perennial.errors.isLeafError e ∧
      methodSet e.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool])⌝)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.bbolt.errors :=
  define_is_pkg_init bboltErrorsInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.bbolt.errors :=
  build_get_is_pkg_init_wf

end go_etcd_io.bbolt.errors

namespace go_etcd_io.etcd.client.pkg.v3.verify

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.client.pkg.v3.verify

namespace github_com.prometheus.client_golang.prometheus

set_option linter.iris.dupNamespace false in
instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus :=
  define_is_pkg_init iprop(True)
set_option linter.iris.dupNamespace false in
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus :=
  build_get_is_pkg_init_wf

end github_com.prometheus.client_golang.prometheus

namespace go_etcd_io.etcd.server.v3.storage.backend

/-- A prometheus `Histogram` as the backend uses it: `Observe(x)` returns (metrics have no effect
the model sees). -/
def histSpec (h : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ x : w64, {{ True }} (App (Val #(methods h.ty go!"Observe" h.v)) (Val #x))
    {{ RET #(); True }}))

instance histSpec_persistent (h : GoInterfaceOk) : Persistent (histSpec (GF := GF) h) := by
  unfold histSpec; infer_instance

/-- The backend's package facts: the commit's histograms of `metrics.go` (`rebalanceSec`,
`spillSec`, `writeSec`, `commitSec`), each a fixed interface value whose `Observe` returns. -/
abbrev backendInit : IProp GF :=
  iprop((∃ h : GoInterfaceOk, globalAddr rebalanceSec ↦□ GoInterface.ok h ∗ histSpec h) ∗
    (∃ h : GoInterfaceOk, globalAddr spillSec ↦□ GoInterface.ok h ∗ histSpec h) ∗
    (∃ h : GoInterfaceOk, globalAddr writeSec ↦□ GoInterface.ok h ∗ histSpec h) ∗
    (∃ h : GoInterfaceOk, globalAddr commitSec ↦□ GoInterface.ok h ∗ histSpec h))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend :=
  define_is_pkg_init backendInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage.backend

end init

end Perennial

/-
Package initialization instances for etcd's lessor (`server/v3/lease`) and the package its types
name that no lower proof module provides: `github.com/Masterminds/semver/v3` (names only: the
lessor's `cluster` interface's `Version`; moved here from the server's `apply/Base.lean` on
2026-10-13). The others are the cache's (`cache/v3/Base.lean`: `zap`, `etcdserverpb`), the
backend's (`storage/backend/Base.lean`) and Perennial's (`sync`, `time`, `context`, `errors`).
`lease`'s instance moved here from mvcc's `Base.lean` (2026-10-13, unit 8 of the backend: the
lessor's KV-facing methods are translated with bodies).

As in those, the package facts are assumptions about package initialization, not proved from
`initialize'`: `leaseInit` states what the proved methods read: the error variables
`ErrLeaseNotFound`, `ErrLeaseExists`, `ErrLeaseTTLTooLarge` (`errors.New(...)`: each a fixed
leaf pointer error whose `Error()` returns, `leaseErrVar`, the shape of the apply package's
`errVarLeaf`; 2026-10-13, unit 9: before, `ErrLeaseNotFound` was only a fixed value), the
variable `forever` (`time.Time{}`, read-only), and the metrics (`metrics.go`: `leaseGranted` and
`leaseRevoked` counters whose `Inc` returns, the histogram `leaseTotalTTLs` whose `Observe`
returns; metrics have no effect the model sees).

Unit 9 adds the instances of the packages the lessor's apply-side methods import:
`api/v3/version` (moved here from the server's `BaseApply.lean`: its `Version`, and now `V3_6`,
fixed read-only values), `lease/leasepb` (types only) and `container/heap` (names only: a
standard-library package Perennial does not translate).
-/
module

public import Code.go_etcd_io.etcd.server.v3.lease
public import GeneratedProof.go_etcd_io.etcd.server.v3.lease
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Base
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.sync
public import Perennial.Proof.time
public import Perennial.Proof.context
public import Perennial.Proof.errors
public import Perennial.Proof.sort
public import Code.go_etcd_io.etcd.api.v3.version
public import GeneratedProof.go_etcd_io.etcd.api.v3.version
public import Code.go_etcd_io.etcd.server.v3.lease.leasepb
public import GeneratedProof.go_etcd_io.etcd.server.v3.lease.leasepb
public import Code.container.heap
public import GeneratedProof.container.heap
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base

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

-- `github.com/Masterminds/semver/v3` (names only: `MustParse`, `Version.LessThan`/`String`)
namespace github_com.Masterminds.semver.v3

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.Masterminds.semver.v3 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.Masterminds.semver.v3 :=
  build_get_is_pkg_init_wf

end github_com.Masterminds.semver.v3

namespace go_etcd_io.etcd.api.v3.version

/-- `api/v3/version` (names-only): the package variables `Version` (the request path's unit 4c:
the server's `start` logs it; moved here from the server's `BaseApply.lean`, 2026-10-13) and
`V3_6` (the lessor's `shouldPersistCheckpoints` compares the cluster's version with it) hold
fixed read-only values. -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version :=
  define_is_pkg_init iprop((∃ v : GoString, globalAddr go_etcd_io.etcd.api.v3.version.Version ↦□ v) ∗
    (∃ v : github_com.Masterminds.semver.v3.Version,
      globalAddr go_etcd_io.etcd.api.v3.version.V3_6 ↦□ v))
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.version :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.api.v3.version

-- `server/v3/lease/leasepb` (types only: the lease's protobuf message)
namespace go_etcd_io.etcd.server.v3.lease.leasepb

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease.leasepb :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease.leasepb :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.lease.leasepb

-- `container/heap` (names only)
namespace container.heap

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.container.heap :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.container.heap :=
  build_get_is_pkg_init_wf

end container.heap

namespace go_etcd_io.etcd.server.v3.lease

/-- The error variable `g` holds an `errors.New` error: a leaf pointer error without an `Is`
method whose `Error()` returns (the shape of the apply package's `errVarLeaf`, which the lease
package cannot import). -/
def leaseErrVar (g : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗
    ⌜_root_.Perennial.errors.IsPointerError e ∧ _root_.Perennial.errors.isLeafError e ∧
      methodSet e.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool])⌝ ∗
    {{ True }} (App (Val #(methods e.ty go!"Error" e.v)) (Val #()))
      {{ (msg : GoString), RET #msg; True }})

instance leaseErrVar_persistent (g : GoString) : Persistent (leaseErrVar (GF := GF) g) := by
  unfold leaseErrVar; infer_instance

/-- A prometheus `Counter`: `Inc()` returns (metrics have no effect the model sees). -/
def counterSpec (c : GoInterfaceOk) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods c.ty go!"Inc" c.v)) (Val #())) {{ RET #(); True }}))

instance counterSpec_persistent (c : GoInterfaceOk) : Persistent (counterSpec (GF := GF) c) := by
  unfold counterSpec; infer_instance

/-- The lessor package's facts: the error variables `ErrLeaseNotFound`, `ErrLeaseExists`,
`ErrLeaseTTLTooLarge` (`leaseErrVar`), `forever` (the zero `time.Time`), the counters
`leaseGranted`, `leaseRevoked` and the histogram `leaseTotalTTLs`. -/
abbrev leaseInit : IProp GF :=
  iprop(leaseErrVar ErrLeaseNotFound ∗ leaseErrVar ErrLeaseExists ∗
    leaseErrVar ErrLeaseTTLTooLarge ∗
    globalAddr forever ↦□ (zero_val _root_.Perennial.time.Time) ∗
    (∃ c : GoInterfaceOk, globalAddr leaseGranted ↦□ GoInterface.ok c ∗ counterSpec c) ∗
    (∃ c : GoInterfaceOk, globalAddr leaseRevoked ↦□ GoInterface.ok c ∗ counterSpec c) ∗
    (∃ h : GoInterfaceOk, globalAddr leaseTotalTTLs ↦□ GoInterface.ok h ∗
      go_etcd_io.etcd.server.v3.storage.backend.histSpec h))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease :=
  define_is_pkg_init leaseInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.lease

end init

end Perennial

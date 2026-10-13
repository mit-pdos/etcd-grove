/-
Package initialization instances for etcd's lessor (`server/v3/lease`) and the package its types
name that no lower proof module provides: `github.com/Masterminds/semver/v3` (names only: the
lessor's `cluster` interface's `Version`; moved here from the server's `apply/Base.lean` on
2026-10-13). The others are the cache's (`cache/v3/Base.lean`: `zap`, `etcdserverpb`), the
backend's (`storage/backend/Base.lean`) and Perennial's (`sync`, `time`, `context`, `errors`).
`lease`'s instance moved here from mvcc's `Base.lean` (2026-10-13, unit 8 of the backend: the
lessor's KV-facing methods are translated with bodies).

As in those, the package facts are assumptions about package initialization, not proved from
`initialize'`: `leaseInit` states what the proved methods read, the error variable
`ErrLeaseNotFound` (`errors.New("lease not found")`), a fixed non-nil error.
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

namespace go_etcd_io.etcd.server.v3.lease

/-- The lessor package's facts: `ErrLeaseNotFound` holds a fixed non-nil error. -/
abbrev leaseInit : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr ErrLeaseNotFound ↦□ GoInterface.ok e)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease :=
  define_is_pkg_init leaseInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.lease

end init

end Perennial

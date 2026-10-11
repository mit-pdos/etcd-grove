/-
Package initialization for etcd's server `txn` package (`server/v3/etcdserver/txn`: the
server's `Range`, `Put`, `DeleteRange` and `Txn` over the mvcc core). Every package it imports
already has its instance: mvcc's (`storage/mvcc/Base.lean`: mvcc, `traceutil`, `lease`,
`schedule`, prometheus), the cache's (`cache/v3/Base.lean`: `zap`, `proto`, `mvccpb`,
`etcdserverpb`), `etcdserver/errors/Base.lean` and
Perennial's (`context`, `time`, `bytes`, `math`, `sort`, `fmt`).

As in those, the package facts are assumptions about package initialization, not proved from
`initialize'` (the package's initializer runs the axiomatized initializers of its metrics).
`txnInit` states what the translated code reads of the package variables: nothing of its own
(the metrics `slowApplies`, `applySec`, `rangeSec` are read only by the names-only `util.go`
and `metrics.go`), and two error variables of imported packages the txn code returns, each a
fixed non-nil error: `lease.ErrLeaseNotFound` (`checkLease`) and `etcdserver/errors`'
`ErrKeyNotFound` (`checkAndGetPrevKV`). They are stated here, not in their packages' facts:
`lease`'s are mvcc's (`True`) and `errors`' the server's (`ErrNoSpace`), which this package
leaves as they are; the facts hold once the txn package is initialized, its imports first.
mvcc's `ErrFutureRev`/`ErrCompacted` (`checkRange`) are mvcc's facts (`mvccInit`).
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.txn
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.txn
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Base
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.time
public import Perennial.Proof.bytes
public import Perennial.Proof.math
public import Perennial.Proof.sort
public import Perennial.Proof.fmt

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

namespace go_etcd_io.etcd.server.v3.etcdserver.txn

/-- The txn package's facts: the error variables of its imports it returns, each a fixed
non-nil error (`lease.ErrLeaseNotFound`, `etcdserver/errors.ErrKeyNotFound`). -/
abbrev txnInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound ↦□ GoInterface.ok e))

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn :=
  define_is_pkg_init txnInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.txn

end init

end Perennial

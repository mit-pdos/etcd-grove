/-
Package initialization for etcd's server `txn` package (`server/v3/etcdserver/txn`: the
server's `Range`, `Put`, `DeleteRange` and `Txn` over the mvcc core). Every package it imports
already has its instance: mvcc's (`storage/mvcc/Base.lean`: mvcc, `traceutil`, `lease`,
`schedule`, prometheus), the cache's (`cache/v3/Base.lean`: `zap`, `proto`, `mvccpb`,
`etcdserverpb`), `etcdserver/errors/Base.lean` and
Perennial's (`context`, `time`, `bytes`, `math`, `sort`, `fmt`).

As in those, the package facts are assumptions about package initialization, not proved from
`initialize'` (the package's initializer runs the axiomatized initializers of its metrics).
`txnInit` states what the translated code reads of the package variables: of its own, the
counter `slowApplies` (`util.go`'s `warnOfExpensiveGenericRequest` calls its `Inc`; unit P4,
2026-10-14: `prometheus.NewCounter` at init, a counter whose `Inc` returns, `lease.counterSpec`;
and, since prove-etcdserver (2026-11-20), the histogram vectors `applySec` and `rangeSec` with their
label names, which `metrics.go`'s translated observers read), and two error variables of imported packages the txn code returns, each a
fixed non-nil error: `lease.ErrLeaseNotFound` (`checkLease`) and `etcdserver/errors`'
`ErrKeyNotFound` (`checkAndGetPrevKV`). They are stated here, not in their packages' facts:
`lease`'s are mvcc's (`True`) and `errors`' the server's (`ErrNoSpace`), which this package
leaves as they are; the facts hold once the txn package is initialized, its imports first.
mvcc's `ErrFutureRev`/`ErrCompacted` (`checkRange`) are mvcc's facts (`mvccInit`).
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.txn
public import Perennial.Proof.reflect.Base
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.txn
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.errors.Base
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.time
public import Perennial.Proof.bytes
public import Perennial.Proof.math
public import Perennial.Proof.sort
public import Perennial.Proof.fmt
public import Perennial.Proof.strings
public import Proof.go_etcd_io.etcd.server.v3.lease.Base
public import Proof.github_com.prometheus.client_golang.prometheus.Labels

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

-- (`reflect`'s instance: `Proof/reflect/PkgInit.lean`, shared)

namespace go_etcd_io.etcd.server.v3.etcdserver.txn

/-- The txn package's facts: the error variables of its imports it returns, each a fixed
non-nil error (`lease.ErrLeaseNotFound`, `etcdserver/errors.ErrKeyNotFound`), its counter
`slowApplies`, whose `Inc` returns, and (prove-etcdserver, 2026-11-20) its histogram vectors
`applySec` and `rangeSec` with their label names (what `metrics.go`'s observers' `WithLabelValues`
needs). -/
abbrev txnInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.server.v3.etcdserver.errors.ErrKeyNotFound ↦□ GoInterface.ok e) ∗
    (∃ c : GoInterfaceOk, globalAddr slowApplies ↦□ GoInterface.ok c ∗
      go_etcd_io.etcd.server.v3.lease.counterSpec c) ∗
    (∃ hv : Loc, globalAddr applySec ↦□ hv ∗
      ⌜EtcdGrove.prometheus.vecLabels hv [go!"version", go!"op", go!"success"]⌝) ∗
    (∃ hv : Loc, globalAddr rangeSec ↦□ hv ∗ ⌜EtcdGrove.prometheus.vecLabels hv [go!"success"]⌝))

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn :=
  define_is_pkg_init txnInit
instance get_isPkgInit_wf_inst [EtcdGrove.prometheus.PromRegGS GF] :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.txn

end init

end Perennial

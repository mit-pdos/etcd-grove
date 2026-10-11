/-
Package initialization instances for etcd's mvcc store (`server/v3/storage/mvcc`) and the
packages it imports that no other proof module provides: `pkg/v3/traceutil`, `server/v3/lease`,
`pkg/v3/schedule`, prometheus's `client_golang/prometheus` and opentelemetry's `otel/trace` (all
names and types only). The others are the interval tree's (`pkg/v3/adt/Base.lean`), the
cache's (`cache/v3/Base.lean`: `zap`, `proto`, `mvccpb`, `client/v3`), the server's
(`etcdserver/Base.lean`: `backend`, `schema`, `client/pkg/v3/verify`), the btree's
(`btree/Init.lean`) and Perennial's (`sync`, `bytes`, `context`, `errors`, `fmt`, `time`,
`encoding/binary`, `math`, `strings`).

As in those, the package facts are assumptions about package initialization, not proved from
`initialize'` (mvcc's initializer runs the axiomatized initializers of its untranslated
variables). `mvccInit` states what the KV core reads of them: the three error variables, each
a fixed non-nil error, and the prometheus counters and gauges of `metrics.go` the transactions
and the key index update, each a fixed interface value whose `Inc`/`Dec`/`Add` return
(`counterSpec`, `gaugeSpec`: metrics have no effect here); and the two configuration defaults
`NewStore` reads (`defaultCompactionBatchLimit`, `defaultCompactionSleepInterval`), any values.
-/
module

public import Code.go_etcd_io.etcd.server.v3.storage.mvcc
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.mvcc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Base
public import Perennial.Proof.time
public import Perennial.Proof.bytes
public import Perennial.Proof.math
public import Perennial.Proof.strings

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

namespace go_etcd_io.etcd.pkg.v3.traceutil

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.traceutil

namespace go_etcd_io.etcd.server.v3.lease

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.lease

namespace go_etcd_io.etcd.pkg.v3.schedule

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.pkg.v3.schedule

namespace github_com.prometheus.client_golang.prometheus

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.prometheus.client_golang.prometheus :=
  build_get_is_pkg_init_wf

end github_com.prometheus.client_golang.prometheus

namespace go_opentelemetry_io.otel.trace

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_opentelemetry_io.otel.trace :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_opentelemetry_io.otel.trace :=
  build_get_is_pkg_init_wf

end go_opentelemetry_io.otel.trace

namespace go_etcd_io.etcd.server.v3.storage.mvcc

/-- A prometheus `Counter` as the KV core uses it: `Inc()` and `Add(x)` return. -/
def counterSpec (c : GoInterfaceOk) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods c.ty go!"Inc" c.v)) (Val #())) {{ RET #(); True }}) ∗
    □ (∀ x : w64, {{ True }} (App (Val #(methods c.ty go!"Add" c.v)) (Val #x)) {{ RET #(); True }}))

instance counterSpec_persistent (c : GoInterfaceOk) : Persistent (counterSpec (GF := GF) c) := by
  unfold counterSpec; infer_instance

/-- A prometheus `Gauge` as the KV core uses it: `Inc()`, `Dec()` and `Add(x)` return. -/
def gaugeSpec (g : GoInterfaceOk) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods g.ty go!"Inc" g.v)) (Val #())) {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods g.ty go!"Dec" g.v)) (Val #())) {{ RET #(); True }}) ∗
    □ (∀ x : w64, {{ True }} (App (Val #(methods g.ty go!"Add" g.v)) (Val #x)) {{ RET #(); True }}))

instance gaugeSpec_persistent (g : GoInterfaceOk) : Persistent (gaugeSpec (GF := GF) g) := by
  unfold gaugeSpec; infer_instance

/-- mvcc's package facts: the error variables `ErrRevisionNotFound` (`key_index.go`),
`ErrCompacted` and `ErrFutureRev` (`kvstore.go`), each a fixed non-nil error; and the metrics
of `metrics.go` the KV core updates: the gauge `keysGauge` (the key index), the counters
`txnCounter`, `rangeCounter`, `putCounter`, `deleteCounter` and the gauge `totalPutSizeGauge`
(the transactions' `End`); and the variables `defaultCompactionBatchLimit` and
`defaultCompactionSleepInterval` (`kvstore.go`) `NewStore` reads, read-only (only tests change
them), their values unconstrained (the store's configuration is not modelled). -/
abbrev mvccInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk, globalAddr ErrRevisionNotFound ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok e) ∗
    (∃ g : GoInterfaceOk, globalAddr keysGauge ↦□ GoInterface.ok g ∗ gaugeSpec g) ∗
    (∃ c : GoInterfaceOk, globalAddr txnCounter ↦□ GoInterface.ok c ∗ counterSpec c) ∗
    (∃ c : GoInterfaceOk, globalAddr rangeCounter ↦□ GoInterface.ok c ∗ counterSpec c) ∗
    (∃ c : GoInterfaceOk, globalAddr putCounter ↦□ GoInterface.ok c ∗ counterSpec c) ∗
    (∃ c : GoInterfaceOk, globalAddr deleteCounter ↦□ GoInterface.ok c ∗ counterSpec c) ∗
    (∃ g : GoInterfaceOk, globalAddr totalPutSizeGauge ↦□ GoInterface.ok g ∗ gaugeSpec g) ∗
    (∃ n : w64, globalAddr defaultCompactionBatchLimit ↦□ n) ∗
    (∃ d : w64, globalAddr defaultCompactionSleepInterval ↦□ d))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc :=
  define_is_pkg_init mvccInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage.mvcc

end init

end Perennial

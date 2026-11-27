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
`ErrNotPrimary` (2026-11-01), `ErrLeaseNotFound`, `ErrLeaseExists`, `ErrLeaseTTLTooLarge` (`errors.New(...)`: each a fixed
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
public import Proof.errors.NewVarCell
public import GeneratedProof.go_etcd_io.etcd.server.v3.lease
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Base
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.sync
public import Perennial.Proof.time
public import Perennial.Proof.context
public import Perennial.Proof.errors
public import Perennial.Proof.sort
public import Code.go_etcd_io.etcd.api.v3.version
public import Proof.go_etcd_io.etcd.api.v3.version.PkgInit
public import Code.go_etcd_io.etcd.server.v3.lease.leasepb
public import GeneratedProof.go_etcd_io.etcd.server.v3.lease.leasepb
public import Code.container.heap
public import GeneratedProof.container.heap
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Proof.github_com.Masterminds.semver.v3.PkgInit
public import Proof.go_etcd_io.etcd.api.v3.version.PkgInit
public import Proof.container.heap.PkgInit

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


-- `api/v3/version`'s instances are in `api/v3/version/PkgInit.lean` (prove-initleft, 2026-11-21: `storage/schema`,
-- below this module, imports it).

-- `server/v3/lease/leasepb`'s instances are in the server's `Base.lean` (schema imports it, 2026-11-19).

-- `container/heap`'s instance (names only): `Proof/container/heap/PkgInit.lean` (L1, 2026-11-24)

namespace go_etcd_io.etcd.server.v3.lease

/-- The error variable `g` holds an `errors.New` error: a leaf pointer error without an `Is`
method (nor a `GRPCStatus` one: k8s etcd3 7c, HS-6) whose `Error()` returns one string (fromerror-stable, 2026-11-06; the shape of the apply package's `errVarLeaf`, which the lease
package cannot import). -/
def leaseErrVar (g : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e ∗
    ⌜_root_.Perennial.errors.IsPointerError e ∧ _root_.Perennial.errors.isLeafError e ∧
      methodSet e.ty !! go!"Is" ≠ some (go.Signature [go.error] false [go.bool]) ∧
      methodSet e.ty !! go!"GRPCStatus" = none ∧
      -- (premise-fixes-4) nor a `Format` one (`fmt` prints it with its `Error`); (fmt soundness 2)
      -- its `Error` is `Error() string`
      (methodSet e.ty !! go!"Format" = none ∧
        methodSet e.ty !! go!"Error" = some (go.signature.Signature [] false [go.string]))⌝ ∗
    ∃ m : GoString, □ ∀ Φ : val → IProp GF, ▷ Φ #m -∗
      WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

instance leaseErrVar_persistent (g : GoString) : Persistent (leaseErrVar (GF := GF) g) := by
  unfold leaseErrVar; infer_instance

/-- A prometheus `Counter`: `Inc()` returns (metrics have no effect the model sees). -/
def counterSpec (c : GoInterfaceOk) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods c.ty go!"Inc" c.v)) (Val #())) {{ RET #(); True }}))

instance counterSpec_persistent (c : GoInterfaceOk) : Persistent (counterSpec (GF := GF) c) := by
  unfold counterSpec; infer_instance

/-- (prove-ps2-newlessor3, 2026-11-21) **The rates and intervals of `lessor.go`** (`var`s, for etcd's
tests; only the initializer writes them): `defaultLeaseRevokeRate`, `leaseCheckpointRate` and
`maxLeaseCheckpointBatchSize` at `1000`, the default intervals at some value: what `newLessor` and the
expiry loop read. In `leaseInit` with `forever` (so that the clients' positional patterns stay). -/
abbrev leaseConsts : IProp GF :=
  iprop(globalAddr defaultLeaseRevokeRate ↦□ (W64 1000) ∗ globalAddr leaseCheckpointRate ↦□ (W64 1000) ∗
    globalAddr maxLeaseCheckpointBatchSize ↦□ (W64 1000) ∗
    (∃ d : w64, globalAddr defaultLeaseCheckpointInterval ↦□ d) ∗
    (∃ d : w64, globalAddr defaultExpiredleaseRetryInterval ↦□ d))

/-- The lessor package's facts: the error variables `ErrLeaseNotFound`, `ErrLeaseExists`,
`ErrLeaseTTLTooLarge` (`leaseErrVar`), `forever` (the zero `time.Time`), the counters
`leaseGranted`, `leaseRevoked` and the histogram `leaseTotalTTLs`; `ErrLeaseNotFound`'s message
cell (`errVarCell`, D19k: what tells it apart from the server's `ErrNoSpace`); `ErrNotPrimary`
(`leaseErrVar`; the lease-renew plan, 2026-11-01: `LeaseRenew` returns it); (prove-ps2-renew,
2026-11-21) the counter `leaseRenewed` (`Renew`'s `Inc()`), beside `leaseRevoked` (grouped with it,
so that the clients' patterns, which name the facts by position, stay as they were). -/
abbrev leaseInit : IProp GF :=
  iprop(leaseErrVar ErrLeaseNotFound ∗ leaseErrVar ErrLeaseExists ∗
    leaseErrVar ErrLeaseTTLTooLarge ∗
    (globalAddr forever ↦□ (zero_val _root_.Perennial.time.Time) ∗ leaseConsts) ∗
    (∃ c : GoInterfaceOk, globalAddr leaseGranted ↦□ GoInterface.ok c ∗ counterSpec c) ∗
    ((∃ c : GoInterfaceOk, globalAddr leaseRevoked ↦□ GoInterface.ok c ∗ counterSpec c) ∗
      (∃ c : GoInterfaceOk, globalAddr leaseRenewed ↦□ GoInterface.ok c ∗ counterSpec c)) ∗
    (∃ h : GoInterfaceOk, globalAddr leaseTotalTTLs ↦□ GoInterface.ok h ∗
      go_etcd_io.etcd.server.v3.storage.backend.histSpec h) ∗
    EtcdGrove.errVarCell ErrLeaseNotFound go!"lease not found" ∗
    EtcdGrove.errVarCell ErrLeaseExists go!"lease already exists" ∗
    EtcdGrove.errVarCell ErrLeaseTTLTooLarge go!"too large lease TTL" ∗ leaseErrVar ErrNotPrimary)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease :=
  define_is_pkg_init leaseInit
instance get_isPkgInit_wf_inst [EtcdGrove.prometheus.PromRegGS GF] : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.lease

end init

end Perennial

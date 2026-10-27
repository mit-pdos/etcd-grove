/-
Package initialization for etcd's gRPC KV service (`server/v3/etcdserver/api/v3rpc`: the
handlers of `key.go`, the request checks, the response header, `togRPCError`). Lean-first (no
Rocq counterpart); plan: `notes/decisions.md`, "The request path".

Every package it imports already has its instance: the server's (`etcdserver/BaseApply.lean`:
`etcdserver`, with the request path's facts `srvInit`), the apply package's and the txn
package's, the cache's (`etcdserverpb`, `rpctypes`, grpc's `codes` and `status`), the interval
tree's (`pkg/v3/adt/Base.lean`) and Perennial's (`context`, `errors`).

As elsewhere, the package fact is an assumption about package initialization, not proved from
`initialize'` (which runs the axiomatized initializers of the package's variables, the error
map among them). `v3rpcInit` states what the translated code reads of package variables: its
own error map `toGRPCErrorMap` (a `map[error]error` literal over sixty error variables of seven
packages, names only: a fixed map whose values are non-nil errors), and the `rpctypes` errors
the checks return, each a fixed non-nil error (stated here rather than in `rpctypes`' facts,
which the cache's proofs destructure by position).
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.BaseGrpc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.BaseStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.BaseWatch
public import Proof.math.rand.Base

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

-- `unicode/utf8` (names only; unit P3b: the unary interceptor's `utf8.ValidString`)
instance utf8_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.unicode.utf8 :=
  define_is_pkg_init iprop(True)
instance utf8_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.unicode.utf8 :=
  build_get_is_pkg_init_wf

-- (`math/rand`'s instance: `Proof/math/rand/Base.lean`, since 2026-10-27)

namespace go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc

/-- The package variable `g` holds a fixed non-nil error (persistent). -/
def errVarSet (g : GoString) : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr g ↦□ GoInterface.ok e)

instance errVarSet_persistent (g : GoString) : Persistent (errVarSet (GF := GF) g) := by
  unfold errVarSet; infer_instance

/-- **The gRPC error map** (`toGRPCErrorMap`, `util.go`): a fixed map from the server's errors to
gRPC errors, every value a non-nil error (each an `rpctypes.ErrGRPC*`/`ErrTooManyRequests`/
`ErrMemberNotEnoughStarted`, all `status` errors). Which keys it has is left open: `togRPCError`
returns the mapped error for a key, or `status.Error(codes.Unknown, err.Error())`, both non-nil,
and the handlers' specs say no more of an error. -/
def grpcErrMap : IProp GF :=
  iprop(∃ (mp : Loc) (M : GMap GoInterface GoInterface),
    globalAddr toGRPCErrorMap ↦□ mp ∗ mp ↦$□ M ∗
    ⌜∀ k v, M !! k = some v → v ≠ GoInterface.nil⌝)

/-- **The `rpctypes` errors the checks return** (`checkRangeRequest`, ..., `checkIntervals`,
`checkRequestOp`), each a fixed non-nil error. -/
abbrev checkErrVars : IProp GF :=
  iprop(errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCEmptyKey ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidSortOption ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCValueProvided ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCLeaseProvided ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCTooManyOps ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCDuplicateKey ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCKeyNotFound)

/-- **The protobuf enumerations' name maps** `checkRangeRequest` looks the sort order and target
up in (`etcdserverpb.RangeRequest_SortOrder_name`, `RangeRequest_SortTarget_name`: generated
`map[int32]string` literals, names only here): fixed maps whose keys are the enumerations'
values, `NONE`, `ASCEND`, `DESCEND` (`0` to `2`) and `KEY`, `VERSION`, `CREATE`, `MOD`, `VALUE`
(`0` to `4`). Stated here rather than in `etcdserverpb`'s facts (the cache's). -/
def sortNameMaps : IProp GF :=
  iprop((∃ (mp : Loc) (M : GMap w32 GoString),
      globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest_SortOrder_name ↦□ mp ∗
      mp ↦$□ M ∗ ⌜∀ k : w32, (M !! k).isSome = true ↔ 0 ≤ sint.Z k ∧ sint.Z k ≤ 2⌝) ∗
    (∃ (mp : Loc) (M : GMap w32 GoString),
      globalAddr go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest_SortTarget_name ↦□ mp ∗
      mp ↦$□ M ∗ ⌜∀ k : w32, (M !! k).isSome = true ↔ 0 ≤ sint.Z k ∧ sint.Z k ≤ 4⌝))

/-- **`context.Canceled` is a pointer error** (`errors.New("context canceled")`, Perennial's
`context.wp_initialize'`, whose package fact keeps only that it is a typed error): what
`errors.Is(err, context.Canceled)` (`togRPCError`) needs of its target (`errors.wp_Is`).
Stated here, an assumption about `context`'s initialization as the rest. -/
def ctxCanceledPtr : IProp GF :=
  iprop(∃ e : GoInterfaceOk, globalAddr _root_.Perennial.context.Canceled ↦□ GoInterface.ok e ∗
    ⌜_root_.Perennial.errors.IsPointerError e⌝)

/-- **What the quota wrapper and the unary interceptors read** (unit P3b): the `rpctypes` errors
they return (`ErrGRPCNoSpace`, `ErrGRPCNotCapable`, `ErrGRPCNotSupportedForLearner`,
`ErrGRPCInvalidClientAPIVersion`, `ErrGRPCNoLeader`: fixed non-nil errors), the metadata keys
and value they compare with (`rpctypes.MetadataClientAPIVersionKey`, `MetadataRequireLeaderKey`,
`MetadataHasLeader`: fixed strings), and the counter vector `clientRequests` (`metrics.go`), as
the rest stated here. -/
def interceptorVars : IProp GF :=
  iprop(errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoSpace ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNotCapable ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNotSupportedForLearner ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidClientAPIVersion ∗
    errVarSet go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCNoLeader ∗
    (∃ k : GoString,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataClientAPIVersionKey ↦□ k) ∗
    (∃ k : GoString,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataRequireLeaderKey ↦□ k) ∗
    (∃ k : GoString, globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.MetadataHasLeader ↦□ k) ∗
    (∃ cv : Loc, globalAddr clientRequests ↦□ cv ∗
      ⌜EtcdGrove.prometheus.vecLabels cv [go!"type", go!"client_api_version"]⌝))

instance interceptorVars_persistent : Persistent (interceptorVars (GF := GF)) := by
  unfold interceptorVars; infer_instance

instance grpcErrMap_persistent : Persistent (grpcErrMap (GF := GF)) := by
  unfold grpcErrMap; infer_instance
instance sortNameMaps_persistent : Persistent (sortNameMaps (GF := GF)) := by
  unfold sortNameMaps; infer_instance
instance ctxCanceledPtr_persistent : Persistent (ctxCanceledPtr (GF := GF)) := by
  unfold ctxCanceledPtr; infer_instance

/-- **The package facts `watch.go` reads, but `io.EOF`** (persistent; D19j, 2026-10-18: until
then the premise `watchVars` of the watch path's results, now `v3rpc`'s): the `auth` and `mvcc`
errors it compares with or reports (pointer leaves, `errVarLeaf`, from their packages' facts),
the `rpctypes` errors whose `Error()` it calls (`msgErrVar`, from `rpctypes`' fact), its metrics
(`streamFailures`, the four histograms: their initializers' trust-boundary axioms `<X>_init`),
`traceutil.Tracer`, `context.Canceled`'s pointer error, and the progress interval's lock
(`progressReportIntervalMu`, allocated by the initializer, guarding `progressReportInterval`,
`10 * time.Minute`: `intervalP`), with its reader slots pooled (`intervalPool`, 2026-10-20). `io.EOF` is not among them: Perennial's `io` fact does not
keep it (`v3rpc.eofVar`, `InvWatch.lean`). -/
def _root_.Perennial.EtcdGrove.v3rpc.watchPkgVars : IProp GF :=
  iprop(EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.auth.ErrInvalidAuthToken ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.auth.ErrAuthOldRevision ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.auth.ErrUserEmpty ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.auth.ErrPermissionDenied ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.storage.mvcc.ErrEmptyWatcherRange ∗
    EtcdGrove.errVarLeaf go_etcd_io.etcd.server.v3.storage.mvcc.ErrWatcherDuplicateID ∗
    EtcdGrove.v3rpc.msgErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrCompacted ∗
    EtcdGrove.v3rpc.msgErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCInvalidAuthToken ∗
    EtcdGrove.v3rpc.msgErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCAuthOldRevision ∗
    EtcdGrove.v3rpc.msgErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCUserEmpty ∗
    EtcdGrove.v3rpc.msgErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCPermissionDenied ∗
    EtcdGrove.v3rpc.msgErrVar go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrGRPCWatchCanceled ∗
    (∃ cv : Loc, globalAddr streamFailures ↦□ cv ∗
      ⌜EtcdGrove.prometheus.vecLabels cv [go!"Type", go!"API"]⌝) ∗
    EtcdGrove.v3rpc.histVar watchSendLoopWatchStreamDuration ∗
    EtcdGrove.v3rpc.histVar watchSendLoopWatchStreamDurationPerEvent ∗
    EtcdGrove.v3rpc.histVar watchSendLoopControlStreamDuration ∗
    EtcdGrove.v3rpc.histVar watchSendLoopProgressDuration ∗
    (∃ tr : GoInterfaceOk, globalAddr go_etcd_io.etcd.pkg.v3.traceutil.Tracer ↦□ GoInterface.ok tr) ∗
    ctxCanceledPtr ∗
    EtcdGrove.v3rpc.intervalPool)

instance _root_.Perennial.EtcdGrove.v3rpc.watchPkgVars_persistent :
    Persistent (EtcdGrove.v3rpc.watchPkgVars (GF := GF)) := by
  unfold EtcdGrove.v3rpc.watchPkgVars; infer_instance

/-- The package's facts: the error map, the checks' errors, the sort-name maps,
`context.Canceled`, (unit P3b) what the quota wrapper and the interceptors read, and (item 8,
2026-10-17: until then premises of `getServerMetrics` and `Server`) `metricsServerLock` and what it
guards (`metricsVars`) and `etcdserverpb`'s six `ServiceDesc`s (`svcDescsOk`), and (D19j,
2026-10-18) what `watch.go` reads but `io.EOF` (`watchPkgVars`). -/
abbrev v3rpcInit : IProp GF :=
  iprop(grpcErrMap ∗ checkErrVars ∗ sortNameMaps ∗ ctxCanceledPtr ∗ interceptorVars ∗
    EtcdGrove.v3rpc.metricsVars ∗ EtcdGrove.v3rpc.svcDescsOk ∗ EtcdGrove.v3rpc.watchPkgVars)

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc :=
  define_is_pkg_init v3rpcInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc

end init


end Perennial

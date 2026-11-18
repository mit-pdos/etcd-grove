/-
The contracts of the components the apply package calls through interfaces or names-only
struct pointers (`server/v3/etcdserver/apply`): the trust boundary, each a persistent predicate
of triples (as the txn package's `isTxnLessor`). Lean-first (no Rocq counterpart); plan:
`notes/decisions.md`, "The server's apply".

**The hook's contract** (`csContract P f Pre Q Post`): the shape of every write to the backend
under its batch lock, the apply thread's protocol (`apply.Apply.spec`): the caller hands the
writer its `Pre`, the post-lock hook's triple `{P ∗ Pre} f() {Q}` and the update
`Q ={⊤}=∗ P ∗ Post` (the write itself); a writer that takes the lock (`P`), runs the hook,
writes and unlocks returns `Post`, one that does not write returns `Pre` (`Post ∨ Pre`). `P` is
the batch lock's invariant and `f` the hook, fixed per backend. The txn package's write path
gets the same shape through mvcc (unit A of the apply plan: `hookIs`, `store.Write`): the
definition is mvcc's (`InvStore.lean`), shared by both.

**The components** (each with the hook's `P f` where it writes the backend):
* `isAuthStore st P f RD` (`auth.AuthStore`): the permission checks (`Is*Permitted`, with the
  caller's reader resource `RD` and the key's length bound) return some error and keep the
  caller's `AuthInfo`; `HasRole`, `IsAuthEnabled` (with `RD`), `Revision` return; every
  other method is a `csContract` and returns, for a response, `nil` or a fresh one whose
  `Header` can be set (`respHdrOk`).
* `isApplyLessor le γ P f` (`lease.Lessor`): the txn package's `isTxnLessor`, and `Grant`
  (`csContract`; a lease the lessor knows, `leaseIs`), `Revoke` (`csContract`; at the sole
  writer of `log`, it deletes keys through the store: the sole writer of `log` with deletions
  committed), `Checkpoint` (`csContract`), `Lookup` (nil or a lease, `leaseIs`: its `ID`, and its
  `TTL()` and `Keys()` return).
* `isAlarmStore st P f` (`*v3alarm.AlarmStore`): `Get` returns a slice, `Activate`/`Deactivate`
  are `csContract`s returning nil or an alarm member (`alarmMemberIs`).
* `isCluster c P f` (`*membership.RaftCluster`): `Version` (a pointer, maybe nil), `ID`;
  `SetVersion`, `UpdateAttributes`, `SetDowngradeInfo` are `csContract`s.
* `isRaftStatus rs`, `isSnapshotServer ss`, `isConsistentIndexer ci`: their methods return.
* `isApplyKV kv s γ`: the txn package's `isKV` and the store's `ReadView` (`KV.Rev()` is
  `store.Rev`, verified).
* `isQuota q` (`storage.Quota`): `Available` (some boolean) and `Cost` (some integer) on the three
  request types the appliers pass (any other type panics in `BackendQuota.Cost`).
The `wait.Wait`'s contract is `waitOk` (`Wait.lean`, shared with the server).

**Their errors** (2026-10-12, the merge of unit 2 with the `errors.Is` model): every error the
auth store's and the lessor's methods return is one `errors.Is` can take (`applyErrIs`: in an
error tree, whose errors of a pointer target's type hold pointers). An assumption of the
contracts, as the rest of them: true of etcd's `auth` errors (`errors.New` errors of
`auth/store.go`, `ErrPermissionDenied`, ...) and `lease` errors (`ErrLeaseNotFound`, ...,
`errors.New` too); what `dispatch`'s `errors.Is(ar.Err, mvcc.ErrCompacted)` and the server's
`errors.Is(ar.Err, ErrNoSpace)` need of the applier's result.
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.apply
public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.context
public import Perennial.GeneratedProof.errors
public import GeneratedProof.github_com.Masterminds.semver.v3
public import Perennial.Golang.Theory
public import Code.github_com.prometheus.client_golang.prometheus
public import Code.google_golang_org.protobuf.reflect.protoreflect
public import GeneratedProof.google_golang_org.protobuf.internal.impl
public import Code.google_golang_org.protobuf.runtime.protoimpl
public import Code.go_etcd_io.etcd.api.v3.authpb
public import Code.go_etcd_io.etcd.api.v3.membershippb
public import GeneratedProof.go_etcd_io.etcd.api.v3.mvccpb
public import Code.google_golang_org.grpc.metadata
public import Code.google_golang_org.grpc
public import GeneratedProof.google_golang_org.grpc.chunk1
public import GeneratedProof.google_golang_org.grpc.chunk3
public import Code.go_etcd_io.etcd.api.v3.etcdserverpb
public import Code.net.url
public import Code.go_etcd_io.etcd.client.pkg.v3.types
public import Perennial.GeneratedProof.fmt
public import GeneratedProof.google_golang_org.protobuf.internal.pragma
public import Code.google_golang_org.protobuf.proto
public import Code.go_etcd_io.etcd.pkg.v3.pbutil
public import GeneratedProof.go_uber_org.zap
public import Perennial.GeneratedProof.time
public import Code.go_etcd_io.etcd.pkg.v3.traceutil
public import Perennial.GeneratedProof.log
public import Perennial.GeneratedProof.sync
public import Code.go_etcd_io.etcd.pkg.v3.wait
public import Perennial.GeneratedProof.bytes
public import Code.google_golang_org.grpc.codes
public import Code.google_golang_org.grpc.internal.status
public import Code.google_golang_org.grpc.status
public import Code.go_etcd_io.etcd.api.v3.v3rpc.rpctypes
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.adt
public import Code.golang_org.x.crypto.bcrypt
public import Perennial.GeneratedProof.sort
public import Perennial.GeneratedProof.strconv
public import Perennial.GeneratedProof.strings
public import Perennial.GeneratedProof.sync.atomic
public import Code.go_etcd_io.etcd.server.v3.auth
public import Code.encoding.json
public import Code.go_etcd_io.etcd.pkg.v3.notify
public import Code.go_etcd_io.etcd.server.v3.etcdserver.version
public import Perennial.GeneratedProof.slices
public import Code.go_etcd_io.raft.v3.raftpb
public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.membership
public import Code.go_etcd_io.etcd.server.v3.etcdserver.api
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.backend
public import Perennial.GeneratedProof.encoding.binary
public import Code.go_etcd_io.etcd.client.pkg.v3.verify
public import Code.go_etcd_io.etcd.server.v3.storage.schema
public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm
public import Code.go_etcd_io.etcd.server.v3.etcdserver.cindex
public import Code.go_etcd_io.etcd.server.v3.etcdserver.errors
public import GeneratedProof.go_etcd_io.etcd.server.v3.lease
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.mvcc
public import Perennial.GeneratedProof.math
public import Perennial.GeneratedProof.reflect
public import Code.go_etcd_io.etcd.server.v3.etcdserver.txn
public import GeneratedProof.go_etcd_io.bbolt
public import Code.crypto.tls
public import GeneratedProof.crypto.tls.chunk1
public import Code.go_etcd_io.etcd.client.pkg.v3.transport
public import Code.go_etcd_io.etcd.pkg.v3.featuregate
public import Code.go_etcd_io.etcd.client.pkg.v3.logutil
public import Code.net
public import Code.google_golang_org.grpc.credentials
public import Code.go_etcd_io.etcd.client.v3.credentials
public import Code.go_etcd_io.etcd.client.v3.internal.endpoint
public import Code.go_etcd_io.etcd.client.v3.internal.resolver
public import Code.google_golang_org.grpc.credentials.insecure
public import Code.google_golang_org.grpc.keepalive
public import Code.google_golang_org.grpc.peer
public import Perennial.GeneratedProof.io
public import Code.go_etcd_io.etcd.client.v3
public import GeneratedProof.go_etcd_io.etcd.client.v3.chunk1
public import GeneratedProof.go_etcd_io.etcd.client.v3.chunk4
public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.v3discovery
public import Code.go_opentelemetry_io.contrib.instrumentation.google_golang_org.grpc.otelgrpc
public import Code.go_etcd_io.etcd.server.v3.config
public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.snap
public import GooseLang.Ext.Fs.Impl
public import Code.syscall
public import Code.internal.syscall.unix
public import Code.internal.poll
public import Perennial.GeneratedProof.internal.oserror
public import Code.io.fs
public import Code.os
public import Code.go_etcd_io.etcd.server.v3.storage
public import Proof.reflect.PkgInit
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState
public import Perennial.Proof.errors
public import Proof.errors.NewVarCell
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.time
public import Perennial.Proof.bytes
public import Perennial.Proof.math
public import Perennial.Proof.sort
public import Perennial.Proof.fmt
public import Perennial.Proof.strings
public import Proof.go_etcd_io.etcd.server.v3.lease.Base
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Perennial.Proof.strconv.Base
public import Code.go_etcd_io.raft.v3
public import Perennial.GeneratedProof.crypto.rand
public import Perennial.GeneratedProof.cmp
public import Code.go_etcd_io.raft.v3.quorum
public import GeneratedProof.go_etcd_io.raft.v3.tracker
public import Code.go_etcd_io.raft.v3.confchange
public import Perennial.GeneratedProof.math.big
public import GeneratedProof.go_etcd_io.raft.v3.chunk2
public import Perennial.Code.reflect
public import Perennial.Proof.context
public import Perennial.Proof.sync
public import Perennial.Proof.slices
public import Perennial.Proof.cmp
public import Proof.errors.NewVar
public import Perennial.Proof.encoding.binary
public import Perennial.Proof.math.bits
public import Perennial.Proof.crypto.rand
public import Perennial.Proof.log
public import Perennial.Proof.io
public import Proof.os.PkgInit
public import Perennial.Proof.context.Base
public import Perennial.Std.ByteString
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn
public import Lean
public import Perennial.Std.Attrs
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.MonoNat
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.Token
public import Perennial.Proof.TokSet
public import Perennial.Golang.Theory.String
public import Perennial.Std.GMap
public import Code.encoding.base64
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Perennial.Golang.Defn
public import Proof.go_etcd_io.etcd.server.v3.lease.LeaseRecord
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.lease.MvccShapes
public import Perennial.Proof.slices.SortBasics
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apply

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3
open mvcc.api (MvccName mvccLeases MvccState MvccReachable isMvcc mvccBackend hookIs
  mvccDeleter)
open srvApi (csContractA auBegin auEnd)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-! ## The hook's contract -/

/-! ## Responses -/

/-- A response of type `T` returned by a component: `nil`, or a fresh one whose `Header` the
applier sets (`resp.Header = a.newHeader()`). -/
def respHdrOk (T : Type) (resp : Loc) : IProp GF :=
  iprop(⌜resp = null⌝ ∨ ∃ h : Loc, structFieldRef T go!"Header" resp ↦ h)

/-! ## The backend's write budget -/

/-- **A reader token of the backend `B`** (in place of mvcc's `storeRT γ`, the same of `γ`'s
backend): a component's read, lent and given back. -/
def bkRT (B : mvcc.KBReal) : IProp GF :=
  iprop(backend.rdTok B.γB B.P B.be ∗ backend.bOpen B.γB backend.rdOpen)

/-! ## The auth store -/

/-! ## The lessor -/

/-- The `*lease.Lease` `l` (not nil): its `ID`, and its `TTL()` and `Keys()` return (`Keys` a
fresh slice of the lease's keys, each shorter than `2 ^ 63 - 1`: 2026-10-14, unit A2, the auth
store's `IsPutPermitted` of each needs it; true of every string in memory). -/
def leaseIs (l : Loc) (id : w64) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ structFieldRef lease.Lease go!"ID" l ↦□ id ∗
    □ ({{ True }} (App (Val (l @!! go.GoType.PointerType lease.Lease.ty @!! go!"TTL")) (Val #()))
      {{ (t : w64), RET #t; True }}) ∗
    □ ({{ True }} (App (Val (l @!! go.GoType.PointerType lease.Lease.ty @!! go!"Keys")) (Val #()))
      {{ (sl : GoSlice), RET #sl; ∃ ks : List GoString, sl ↦* ks ∗
          ⌜∀ k ∈ ks, (k.length : Int) < 2 ^ 63 - 1⌝ }}))

/-! ## The alarm store, the cluster, the raft status, the snapshot server -/

/-! ## The KV -/

/-! ## The quota -/

end defs

end apply
end EtcdGrove
end Perennial

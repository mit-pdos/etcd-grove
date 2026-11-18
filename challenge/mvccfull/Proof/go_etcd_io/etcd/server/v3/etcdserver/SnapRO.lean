/-
**The server's snapshot path's persistent bundle and its boot resources** (D22 J1a, 2026-10-26;
`notes/snapshot-sj-plan.md`, "J1a" and "J0 decisions"; `notes/decisions.md`, "D22 J1a"). Lean-first.

`NewServer` makes, and `start`, `run` and `Start` thread (`isServerBuilt`, `isServerRunC`), what the
apply thread's snapshot path (`applySnapshot.specSnapM`, J8a) takes of the server's construction,
with the names it is stated over (`srvSnapBoot`):
* `srvSnapRO` (persistent): the configuration's fields the path reads (its logger, data
  directory, feature gate, quota and apply-duration warning), the snapshotter, the backend hooks
  over the consistent index, the raft storage over the snapshotter (`storage.storageSnap`, from
  `NewStorage`'s contract `rnNewStorageOk`), the member's snapshot directory's invariant at the
  names raft's names give the member (`SrvRaft.snapLoc`) with the server's removal fact
  `snapRmM` (restart S6a; J0 item 3's `srvSnapRm` until then), the stores and their contracts on whichever backend (the alarm store's,
  the auth store's in the environment's mode and, in the mode `off`, its `Recover`, the lessor's,
  the cluster's), the cluster's `Members()` (`srvMembersDir`, `bootOk`'s `Hmembers`), and the
  Key bucket's size bound of every backend at the boot parameters (`keySized`, proved since premise fixes 5: `mvcc.keySized_at`);
* the removal counter's authority at `0` (`γm`, the removal fact's; restart S6a: the member's,
  until then the snapshot-taken counter `γt`);
* (until J8a-6, 2026-11-01) a reader-slot stock (`srvSnapStock`): `lgMu`'s reader slots for the
  snapshots' `AddPeer`s (and until J8a-1 the auth store's reader resource `E.RD`, which the
  snapshots' `NewUberApplier` took until the auth layer's `Apply` borrowed its caller's). Gone: the
  transport's peers borrow from its thread pool (`raftPool`), so an `AddPeer` takes no slot.

The whole configuration read-only (`srvCfgAddr s ↦□ cfg`, which `applySnapshot` reads as a
struct) is the bundle's last conjunct, a rebuild from the two fields `start` writes (J8a-3,
2026-11-01: the fork's `NewWatchServer` no longer writes the configuration,
`nonissues/etcd-cfg-watch-progress-interval-race.md`; `isServerRunC`'s `"#Hsncfg"` holds the fields).
Not here (J1a's findings, `notes/decisions.md`, "D22 J1a"): the meta reads of every backend
(`specSnapM`'s `isMetaBackend` family, false as stated for names the backend was not opened with;
J8a-4).

The stores' apply contracts (`alarmApplyOk`, `authApplyOkM`, `lessorApplyOk`, `clusterApplyOk`),
(Strict M1, 2026-11-06.) Over mvcc's API: a backend is a `mvcc.KBReal` (`d.γB`, `d.P`, `d.be`), the
stores' contracts at the backend tie `srvBkTie d` and the batch lock's invariant `Pk` of every
backend of the epoch (`fun _ => Pk`) in place of the store's names `γ` with `γ.kb = some d`; the
backend's compaction mode and the store's watch flag gone (the API's backend always compacts, its
store has one form), the KV a store handle (`□ isMvcc kv E.γ`), the lessor at the store's lessor
names (`mvccLeases E.γ`); the KV's closer (`srvKVCloser`, `srvKVCloserW`) deleted: what `Restore`
takes of the store, mvcc's open token `mvccOpen`, is the apply thread's (`apply.cmpOwn`).

`memberDirIs`, `srvMembersDir` and `lessorLookupOk` moved here from `InvBoot.lean` and
`SnapApplyDefs.lean` (J1a), unchanged (`memberDirIs` and `srvMembersDir` moved on to
`InvApRes.lean`, 2026-11-01, for `ccMembRes`); `authRecoverOk` is S8d's `srvAuthRecoverOk`, renamed.
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver
public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.context
public import Perennial.Golang.Theory
public import Code.encoding.base64
public import Code.encoding.json
public import Perennial.GeneratedProof.errors
public import Perennial.GeneratedProof.fmt
public import GeneratedProof.github_com.Masterminds.semver.v3
public import Code.github_com.dustin.go_humanize
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
public import Code.go_etcd_io.etcd.api.v3.version
public import Code.go_etcd_io.etcd.client.pkg.v3.logutil
public import Code.net.url
public import Code.go_etcd_io.etcd.client.pkg.v3.types
public import Code.go_etcd_io.etcd.pkg.v3.contention
public import Code.go_etcd_io.etcd.pkg.v3.featuregate
public import GooseLang.Ext.IdIssue.Impl
public import Perennial.GeneratedProof.math
public import Perennial.GeneratedProof.sync.atomic
public import Perennial.GeneratedProof.time
public import Code.go_etcd_io.etcd.pkg.v3.idutil
public import Perennial.GeneratedProof.sync
public import Code.go_etcd_io.etcd.pkg.v3.notify
public import GeneratedProof.google_golang_org.protobuf.internal.pragma
public import Code.google_golang_org.protobuf.proto
public import Code.go_etcd_io.etcd.pkg.v3.pbutil
public import Code.go_etcd_io.etcd.client.pkg.v3.verify
public import GeneratedProof.go_uber_org.zap
public import Code.go_etcd_io.etcd.pkg.v3.schedule
public import Code.go_etcd_io.etcd.pkg.v3.traceutil
public import Perennial.GeneratedProof.log
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
public import Code.go_etcd_io.etcd.server.v3.auth
public import GeneratedProof.go_etcd_io.bbolt
public import Code.crypto.tls
public import GeneratedProof.crypto.tls.chunk1
public import Code.go_etcd_io.etcd.client.pkg.v3.transport
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
public import Code.go_etcd_io.etcd.server.v3.etcdserver.version
public import Perennial.GeneratedProof.slices
public import Code.go_etcd_io.raft.v3.raftpb
public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.membership
public import Code.go_etcd_io.etcd.server.v3.etcdserver.api
public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp.types
public import Perennial.GeneratedProof.encoding.binary
public import Code.github_com.xiang90.probing
public import Code.net.http
public import Code.go_etcd_io.etcd.pkg.v3.httputil
public import Code.go_etcd_io.etcd.pkg.v3.ioutil
public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.snap
public import Perennial.GeneratedProof.crypto.rand
public import Perennial.GeneratedProof.cmp
public import Code.go_etcd_io.raft.v3.quorum
public import GeneratedProof.go_etcd_io.raft.v3.tracker
public import Code.go_etcd_io.raft.v3.confchange
public import Perennial.GeneratedProof.math.big
public import GooseLang.Ext.Fs.Impl
public import Code.syscall
public import Code.internal.syscall.unix
public import Code.internal.poll
public import Perennial.GeneratedProof.internal.oserror
public import Code.io.fs
public import Code.os
public import Code.go_etcd_io.raft.v3
public import GeneratedProof.go_etcd_io.raft.v3.chunk2
public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.v2stats
public import Code.golang_org.x.time.rate
public import Code.internal.bytealg
public import Code.path
public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.backend
public import Code.go_etcd_io.etcd.server.v3.storage.schema
public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm
public import Code.github_com.jonboulle.clockwork
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.mvcc
public import Code.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor
public import Code.go_etcd_io.etcd.server.v3.etcdserver.cindex
public import Code.go_etcd_io.etcd.server.v3.etcdserver.errors
public import GeneratedProof.go_etcd_io.etcd.server.v3.lease
public import Perennial.GeneratedProof.reflect
public import Code.go_etcd_io.etcd.server.v3.etcdserver.txn
public import Code.go_etcd_io.etcd.server.v3.storage
public import Code.go_etcd_io.etcd.server.v3.etcdserver.apply
public import Code.go_etcd_io.etcd.server.v3.etcdserver.read
public import Code.go_etcd_io.etcd.server.v3.features
public import Code.go_etcd_io.etcd.server.v3.lease.leasehttp
public import Code.bufio
public import Code.golang_org.x.sys.unix
public import Perennial.GeneratedProof.internal.stringslite
public import Code.internal.filepathlite
public import Code.path.filepath
public import Code.go_etcd_io.etcd.client.pkg.v3.fileutil
public import Code.hash
public import Code.hash.crc32
public import Code.go_etcd_io.etcd.pkg.v3.crc
public import Code.go_etcd_io.etcd.server.v3.storage.wal.walpb
public import Code.go_etcd_io.etcd.server.v3.storage.wal
public import Code.go_opentelemetry_io.otel.«attribute»
public import Code.go_opentelemetry_io.otel.codes
public import Code.go_opentelemetry_io.otel.trace.embedded
public import Code.go_opentelemetry_io.otel.trace
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Perennial.Proof.errors
public import Proof.errors.NewVarCell
public import Proof.reflect.PkgInit
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState
public import Perennial.Proof.time
public import Perennial.Proof.bytes
public import Perennial.Proof.math
public import Perennial.Proof.sort
public import Perennial.Proof.fmt
public import Perennial.Proof.strings
public import Proof.go_etcd_io.etcd.server.v3.lease.Base
public import Proof.go_etcd_io.etcd.server.v3.auth.Base
public import Perennial.Proof.strconv.Base
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
public import Perennial.Std.Word.LittleEndian
public import Lean
public import Perennial.Std.Attrs
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.MonoNat
public import Perennial.Ghost.SavedProp
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.Token
public import Perennial.GooseLang.Countable
public import Perennial.GooseLang.Receipts
public import Perennial.Ghost.GhostVar
public import Perennial.IrisLib.BI
public import Iris.BI.Lib.Atomic
public import Iris.Instances.Lib.FUpd
public import Perennial.Std.Namespaces
public import Perennial.Proof.time.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.errors.Base
public import Perennial.Proof.encoding.binary.Base
public import TrustedCode.hash.crc32
public import Proof.go_uber_org.zap.PkgInit
public import Proof.github_com.Masterminds.semver.v3.PkgInit
public import Proof.github_com.prometheus.client_golang.prometheus.PkgInit
public import Proof.hash.PkgInit
public import Perennial.Proof.internal.stringslite
public import Proof.syscall.PkgInit
public import Proof.golang_org.x.sys.unix.PkgInit
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.PkgInit
public import Perennial.GooseLang.Lifting
public import Perennial.Golang.Defn.PostLang
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Perennial.Proof.slices.SortBasics
public import Spec.go_uber_org.zap.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LogLemmas
public import Perennial.Std.ListBasics
public import Perennial.Golang.Defn
public import Spec.fmt.Errorf
public import Perennial.Golang.Theory.Chan.Idioms.Handshake
public import Perennial.Std.Qextra
public import Perennial.Proof.TokSet
public import Perennial.Golang.Theory.String
public import Perennial.Std.GMap
public import Proof.go_etcd_io.etcd.server.v3.lease.MvccShapes
public import Perennial.Proof.strings.Base
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Tree
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Defs
public import Perennial.Golang.Theory.Map
public import Perennial.Proof.bytes.Link
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex
public import Perennial.Spec.sync.atomic.Int32__Add
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketRange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact
public import Proof.go_opentelemetry_io.otel.trace.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Model2
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DelKeys
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Perennial.Golang.Theory.Chan.Idioms.Base
public import Perennial.Golang.Theory.Chan
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer
public import Perennial.Golang.Theory.ProofMode
public import Perennial.Proof.math.big
public import Perennial.Golang.Theory.Auto
public import Perennial.Golang.Theory.PostLifting
public import Perennial.Golang.Theory.Mem
public import Perennial.Proof.time.Link
public import Perennial.Proof.context.NewErrorString
public import Perennial.Golang.Theory.Chan.Idioms.Idioms
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env
public import Proof.go_etcd_io.etcd.server.v3.storage.WalDir
public import Perennial.Golang.Theory.TypeSet
public import Perennial.Proof.ThreadPool
public import Proof.net.InvNet
public import Perennial.Code.io
public import Perennial.Code.bytes
public import Perennial.Code.encoding.binary
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Proof.sync.WaitGroupJoin
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Proof.go_etcd_io.etcd.server.v3.lease.LeaseRecord
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndexCut
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor
public import Spec.go_uber_org.zap.Int
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RdPool
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Perennial.Ghost.MonoNat

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3
open mvcc.api (isMvcc mvccLeases)

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The lessor `lp`'s backend contract on whichever backend it is on** (persistent; D22
receiver epochs, S7c; `lease.NewLessor.spec`'s, the trust boundary): as `alarmApplyOk`, its writes
pinned to the backend by the user's half of `le.b` (`lease.lessorBeOn`), which the write right
lends; one write-back token per write, the reader's open share and the write right lent and given
back (the coordinator's decision, 2026-11-06: until then the write right was in the write token,
which a write consumes); the put into `Lease` (a
tracked bucket, D22) with the lease bucket's part (`backend.rbPart d.γB (· = "lease")`, per bucket:
the lessor's put writes `Lease` only; 2026-11-01, the backend-auth-split stage: until then the
whole client half `backend.rbOwn`), given back with the record put (leases T3, L3c, 2026-10-27:
until then the write right lent the half, `srvRestRW`, and the put's effect was not stated; the
real backend's `LockInsideApply` does not need it, its `UnsafePut` does). (The lease-grant stage,
2.12, 2026-11-02, the user's freeze) The counted write-back token is spent and the lent part `RW`
given back (until then spent with it): true of Go, `persistTo(le.b)` reads the field before
`BatchTx()`, and `LockInsideApply`/`Unlock` do not write it (`lease.go:55-61`). -/
def lessorApplyOk (lp : Loc) : IProp GF :=
  iprop(□ ∀ (d : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc) (RW : IProp GF),
    backend.isBackend d.γB d.P W Pk d.be -∗ backend.plHookRO d.γB f -∗ ⌜f ≠ func.nil⌝ -∗
    rwLens RW (lease.lessorBeOn lp d.be) -∗
    lease.lessorBackend lp Pk #f (backend.wbTok d.γB) RW (apply.bkRT d)
      (backend.rbPart d.γB (· = go!"lease")))

-- MERGE-TODO(close): `lean`'s `srvKVCloser`/`srvKVCloserW` (the KV's closer: `mvcc.wsCloser`, or the
-- watchable store's `stopCloser`/`wsWaiter` in compaction mode, over `E.γ.kb`/`E.s`; R-D1 made its
-- `Close` give back the loops' readers and the compaction job's budget) are dropped: over the API
-- the KV's close right is mvcc's open token `mvccOpen E.γ`, the apply thread's `apply.cmpOwn`
-- (`KV.Restore.contract` takes and gives it back, `KV.Close.contract` takes it), and `KV.Close`
-- gives nothing back. What shutdown regains (the plan's risk 1) waits on the user's decision.

end defs

end EtcdGrove
end Perennial

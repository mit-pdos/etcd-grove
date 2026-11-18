/-
**The rest buckets at the applied log** (D22, 2026-10-23: the backend over every bucket;
`notes/decisions.md`, "D22c decided" and "D22 the backend over every bucket carried out").
Lean-first (no Rocq counterpart).

The backend tracks etcd's rest buckets (`mvcc.restBuckets`; `KBReal.P`'s `RB`): a put in, delete
from, creation or deletion of one needs the client's half of them (`backend.rbOwn`). The server's
apply thread holds it with the cluster's in-memory member list (option (i) of "D22c decided":
`membership.clusterMem`, exception 7) at their **model of the applied log** (`restModel`), the
environment's `AEnv.RO` (`srvRestOwn`):

* `restBoot bootLog`: what `bootstrap` and `NewServer`'s constructors leave on a fresh data
  directory: every rest bucket empty but `auth`, which holds the revision `1` (`authBoot`,
  `NewAuthStore`'s `commitRevision`); the in-memory members the boot log's (`memBoot`: the
  members whose JSON the bootstrap entries' contexts are, each keyed by and with its entry's node
  as its id, `ccMemberAt`; 2026-11-02, the backend-auth-split stage);
* `restEntry c0 m`: a normal entry's request through `dispatch` (`apply.restAfter`: the cluster
  version and the member attributes), with `v3` iff above `c0`; a conf change through
  `applyConfChange` (`ccRest`: with `v3`, a validated `AddNode` saves the context's member, a
  validated `RemoveNode` deletes the member and records its removal);
* `restModel c0 bootLog L`: their fold over the raft log `L` from `restBoot bootLog`.

It is a function of the log and of cluster-wide values (`c0`, the boot log): every member's
apply thread computes the same buckets, which is what a snapshot's image carries
(`InvImage.lean`'s `bkRestAt`). Nothing else writes them: the stores' other writers take the
environment's write right `AEnv.RW` (`srvRestRW`: the same half, which the apply thread never
lends), and the workload admits none of their requests (`apply.rqOk`, `plainCover`).
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
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Proof.go_etcd_io.etcd.server.v3.lease.LeaseRecord
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## The membership's model -/

/-! ## The model of the applied log -/

/-! ## The model's steps -/

/-! ## The real backend's tracked buckets -/

section present
variable [GooseExts]

end present

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/- `membership.clusterMem` (the cluster's in-memory members) is defined in the membership
package's `Defs.lean` since D43 M5b (2026-10-26; opaque here until then). -/

/-- **`RW` lends `X`** (persistent; S7c): a write right holding the resources `X` a contract's
writes take and give back (`srvRestRWH` lends each object's part). -/
def rwLens (RW X : IProp GF) : IProp GF := iprop(□ (RW -∗ X ∗ (X -∗ RW)))

end defs

end EtcdGrove
end Perennial

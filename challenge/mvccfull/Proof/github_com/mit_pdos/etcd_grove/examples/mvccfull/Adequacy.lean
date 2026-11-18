/- Lean-first (no Rocq counterpart).

# mvcc's full tester's closed theorem (2026-11-10)

A closed theorem about the operational semantics of `mvccfull`'s program (`examples/mvccfull`): the
package's initialization (which initializes its import closure: mvcc, the lessor, the backend,
zap, ...) followed by `Main()` -- `Run(MainConfig("mvccfull"))`: two members (a leader and a
follower), each a backend in a fresh file, a lessor and a store over it as etcd's server makes them,
the writer's 12000 log steps (puts, deletes, transactions, lease grants and revokes, compactions,
snapshot installs into fresh builder stores, clean restarts), 2 readers per member and 2 watch
streams per member running concurrently, every result of mvcc checked against the tester's model
(a failed check panics), then each member's streams drained and closed, its store closed, reopened
and read in full, and closed -- started from a fresh state (no package initialized, one thread):
for every real execution of `n` steps, the main thread's result, if it has one, is `#()`, no thread
is stuck, and no thread has ended in a panic. So no check of the tester fails, in any
interleaving, within the executions it covers.

**What it covers: each prefix of fewer than `2 ^ 28` steps** (finding mvcc-r3-1, round 3,
2026-11-11). The execution's length is bounded by the hypothesis `n + 2 ≤ 2 ^ 28` (the thread
bound), and a full-size run of `Main` (12000 writer steps, with readers and watch streams on two
members, each over a bbolt-backed store) takes more steps than that. The theorem therefore says no
check fails in the first `2 ^ 28 - 2` steps of any interleaving. It says nothing about a run's later
steps, and in particular it does not say that a complete run of `Main` returns.

As `mvccrand_adequate` (`examples/mvccrand/Adequacy.lean`; `notes/decisions.md`, "mvccrand's closed
theorem"): from `goose_adequacy_start_files` (`Proof/runtime/Start.lean`), with the trivial
extension and a ghost-state bundle `mvccfullGF`, `mvccfull`'s `wp_initialize'` (`Init.lean`, over the
program's package table `PkgTable.lean`) and `mvccfull.wp_Main` (`Link.lean`; `Results.lean`'s
`mvccfull_Main`). The program's fresh files are `FilePaths(MainConfig("mvccfull"))`
(`filePathsM`: the members' two and one per possible snapshot install, `Ops = 12000`), distinct
(`filePaths_main_nodup`).

**Its hypotheses** are mvccrand's, but `sort.Slice.spec` (`mvccfull.wp_Main` takes no hypothesis:
the tester's lease checks compare the lessor's list against the model's without sorting it):
* pure facts of the program's environment: `dbOpenOk` and `dbCloseOk` (bbolt's `Open` and `Close`
  do not fail for the environment's reasons), `dbFilesAbsent` of `Main`'s files (absent at start,
  touched only by the backend) and `verifyEnvOff` (`ETCD_VERIFY` unset), and the execution's length
  (`n + 2 ≤ 2 ^ 28`: the thread bound, and with `N = n + 1` the receipt bound `2 ^ 38`);
* the semantics: `go.Semantics` and the package assumptions (`mvccfull`'s, mvcc's, the server's,
  the cache's).
Nothing beyond mvccrand's. (Until premise fixes 5, 2026-11-10, also the store's key-count premise
`keySized` at every ghost-state instance; now proved, `mvcc.keySized_all`, from bbolt's address-space
bound `backend.rtxSnap_size`.)
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.FilePaths
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.memberPath
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.buildPath
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.mvccfull
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.ApiState
public import Perennial.Proof.sync.RWMutexGuard
public import Perennial.Ghost.MonoList
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.MonoNat
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.sync.WaitGroupTokJoin
public import Iris.BI.BigOp.BigSepList
public import Iris.BI.Lib.Fractional
public import Iris.ProofMode
public import Perennial.Ghost.GhostMap
public import Perennial.Proof.sync.WaitGroupJoin
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.MustUnsafeGetAllLeases
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.mvccrand
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.DelKeys
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer
public import Perennial.Std.ListBasics
public import Perennial.Golang.Theory.Map
public import Perennial.IrisLib.BI
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Model2
public import Spec.go_uber_org.zap.Defs
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Ghost.SavedProp
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.bytes
public import Perennial.GeneratedProof.encoding.binary
public import Perennial.Golang.Theory
public import Code.google_golang_org.protobuf.reflect.protoreflect
public import GeneratedProof.google_golang_org.protobuf.internal.impl
public import Code.google_golang_org.protobuf.runtime.protoimpl
public import Code.go_etcd_io.etcd.api.v3.authpb
public import Perennial.GeneratedProof.context
public import Code.go_etcd_io.etcd.api.v3.membershippb
public import GeneratedProof.go_etcd_io.etcd.api.v3.mvccpb
public import Code.google_golang_org.grpc.metadata
public import Code.google_golang_org.grpc
public import GeneratedProof.google_golang_org.grpc.chunk1
public import GeneratedProof.google_golang_org.grpc.chunk3
public import Code.go_etcd_io.etcd.api.v3.etcdserverpb
public import Perennial.GeneratedProof.fmt
public import Code.go_etcd_io.etcd.client.pkg.v3.verify
public import Perennial.GeneratedProof.errors
public import Code.google_golang_org.grpc.codes
public import Code.google_golang_org.grpc.internal.status
public import Code.google_golang_org.grpc.status
public import Code.go_etcd_io.etcd.api.v3.v3rpc.rpctypes
public import GeneratedProof.go_etcd_io.etcd.pkg.v3.adt
public import GeneratedProof.go_uber_org.zap
public import Code.golang_org.x.crypto.bcrypt
public import Perennial.GeneratedProof.sort
public import Perennial.GeneratedProof.strconv
public import Perennial.GeneratedProof.strings
public import Perennial.GeneratedProof.sync
public import Perennial.GeneratedProof.sync.atomic
public import Perennial.GeneratedProof.time
public import Code.go_etcd_io.etcd.server.v3.auth
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.backend
public import GeneratedProof.google_golang_org.protobuf.internal.pragma
public import Code.google_golang_org.protobuf.proto
public import Code.go_etcd_io.etcd.server.v3.storage.schema
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.RdPool
public import Perennial.ProgramLogic.Bounds
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BboltOptions
public import Spec.go_etcd_io.etcd.server.v3.lease.NewLessor
public import Code.go_etcd_io.etcd.server.v3.etcdserver
public import Code.encoding.base64
public import Code.encoding.json
public import GeneratedProof.github_com.Masterminds.semver.v3
public import Code.github_com.dustin.go_humanize
public import Code.github_com.prometheus.client_golang.prometheus
public import Code.go_etcd_io.etcd.api.v3.version
public import Code.go_etcd_io.etcd.client.pkg.v3.logutil
public import Code.net.url
public import Code.go_etcd_io.etcd.client.pkg.v3.types
public import Code.go_etcd_io.etcd.pkg.v3.contention
public import Code.go_etcd_io.etcd.pkg.v3.featuregate
public import GooseLang.Ext.IdIssue.Impl
public import Perennial.GeneratedProof.math
public import Code.go_etcd_io.etcd.pkg.v3.idutil
public import Code.go_etcd_io.etcd.pkg.v3.notify
public import Code.go_etcd_io.etcd.pkg.v3.pbutil
public import Code.go_etcd_io.etcd.pkg.v3.schedule
public import Code.go_etcd_io.etcd.pkg.v3.traceutil
public import Perennial.GeneratedProof.log
public import Code.go_etcd_io.etcd.pkg.v3.wait
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
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Perennial.Proof.errors
public import Proof.errors.NewVarCell
public import Proof.reflect.PkgInit
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
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.Token
public import Perennial.GooseLang.Countable
public import Perennial.GooseLang.Receipts
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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn
public import Perennial.Proof.slices.SortBasics
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.LogLemmas
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
public import Perennial.Proof.bytes.Link
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex
public import Perennial.Spec.sync.atomic.Int32__Add
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketRange
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact
public import Proof.go_opentelemetry_io.otel.trace.Defs
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Error
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.String
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest
public import Perennial.Golang.Theory.Chan.Idioms.Base
public import Perennial.Golang.Theory.Chan
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
public import Perennial.Spec.time.Ticker__Stop
public import Perennial.Golang.Theory.TypeSet
public import Perennial.Proof.ThreadPool
public import Proof.net.InvNet
public import Perennial.Code.io
public import Perennial.Code.bytes
public import Perennial.Code.encoding.binary
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Proof.go_etcd_io.etcd.server.v3.lease.LeaseRecord
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndexCut
public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor
public import Spec.go_uber_org.zap.Int
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRO
public import Spec.go_uber_org.zap.Logger__Info
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorRecover
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.MainConfig
public import Spec.go_uber_org.zap.NewNop
public import Perennial.Spec.sync.atomic.Int64__Load
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.itoa
public import Proof.container.heap.Defs
public import Proof.container.heap.Init_
public import Perennial.Std.List
public import Perennial.Spec.sync.atomic.LoadInt64
public import Spec.container.heap.Init_
public import Perennial.Proof.sync.RWMutexThreads
public import Spec.time.Time__IsZero
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.MustUnsafePutLease
public import Proof.go_etcd_io.etcd.server.v3.lease.NewLessor
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__scheduleCheckpointIfNeeded
public import Spec.sort.SortAnyLess
public import Spec.sort.StringSlice__Sort
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeDeleteLease
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas
public import Batteries.Data.List.Perm
public import Proof.go_etcd_io.etcd.server.v3.lease.lessor__Stop
public import Proof.go_etcd_io.etcd.server.v3.lease.lessor__scheduleCheckpointIfNeeded
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Model
public import Perennial.Spec.sync.atomic.Int64__Add
public import Perennial.Spec.sort.Strings
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Spec.time.Sleep
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Stop
public import Perennial.Proof.sync.Results
public import Proof.go_etcd_io.etcd.server.v3.storage.schema.MustUnsafeGetAllLeases
public import Proof.go_etcd_io.etcd.server.v3.storage.schema.MustUnsafePutLease
public import Proof.go_etcd_io.etcd.server.v3.storage.schema.UnsafeDeleteLease
public import Proof.sort.StringSlice__Sort
public import Proof.time.Time__IsZero
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base
public import Proof.go_uber_org.zap.NewNop
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.HashDefs
public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Hist
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchBatch
public import Proof.fmt.ErrorfWrap
public import Proof.github_com.dustin.go_humanize.Bytes
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.hashStorage__Store
public import Spec.go_uber_org.zap.Logger__Panic
public import Spec.go_uber_org.zap.Int64
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.kvHasher__Hash
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.kvHasher__WriteKeyValue
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchGroup
public import Spec.google_golang_org.protobuf.proto.Unmarshal
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.newKVHasher
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Defs
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Tree
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init
public import Proof.google_golang_org.protobuf.proto.Marshal
public import Proof.google_golang_org.protobuf.proto.Unmarshal
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Verify
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Base
public import Perennial.Proof.context.Results
public import Spec.fmt.ErrorfWrap
public import Spec.google_golang_org.protobuf.proto.Marshal
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.RdSupply
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.hashStorage__Store
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CutDefs
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newKVHasher
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.kvHasher__WriteKeyValue
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.kvHasher__Hash
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Uint32
public import Spec.github_com.dustin.go_humanize.Bytes
public import Spec.time.Time__Unix
public import Proof.time.Time__Unix
public import Proof.go_opentelemetry_io.otel.trace.SpanFromContext
public import Proof.go_etcd_io.etcd.cache.v3.InvBtree
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Verify
public import Spec.go_opentelemetry_io.otel.trace.SpanFromContext
public import Perennial.Spec.time.NewTicker
public import Perennial.Spec.time.Ticker__Reset
public import Proof.go_uber_org.zap.Duration
public import Proof.go_uber_org.zap.Error
public import Proof.go_uber_org.zap.Int
public import Proof.go_uber_org.zap.Int64
public import Proof.go_uber_org.zap.Logger__Error
public import Proof.go_uber_org.zap.Logger__Info
public import Proof.go_uber_org.zap.Logger__Panic
public import Proof.go_uber_org.zap.Logger__Warn
public import Proof.go_uber_org.zap.String
public import Proof.go_uber_org.zap.Uint32
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ValidateCalledInsideApply
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ValidateCalledOutSideApply
public import Spec.go_etcd_io.bbolt.DB__Close_kv
public import Spec.go_etcd_io.bbolt.Tx__Size_kv
public import Spec.go_etcd_io.bbolt.Tx__DB_kv
public import Spec.go_etcd_io.bbolt.DB__Stats_kv
public import Spec.go_etcd_io.bbolt.DB__Info_kv
public import Spec.go_etcd_io.bbolt.DB__Begin_kv
public import Spec.go_uber_org.zap.Logger__Fatal
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.newBoltLoggerZap
public import Spec.go_etcd_io.bbolt.Open_kv
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.MutexLit
public import Spec.go_etcd_io.bbolt.Tx__Bucket_kvr
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_kvr
public import Spec.go_etcd_io.bbolt.Tx__Rollback_kv
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.ValidateCalledInsideApply
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.ValidateCalledOutSideApply
public import Spec.go_etcd_io.bbolt.Tx__CreateBucketIfNotExists_kv
public import Spec.go_uber_org.zap.Stringer
public import Spec.go_etcd_io.bbolt.Tx__Bucket_kvw
public import Spec.go_etcd_io.bbolt.Bucket__Delete_kv
public import Spec.go_uber_org.zap.Stack
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_kvw
public import Spec.go_etcd_io.bbolt.Tx__Commit_kv
public import Spec.go_etcd_io.bbolt.Tx__Stats_kv
public import Spec.time.Duration__Seconds
public import Spec.go_etcd_io.bbolt.Bucket__Put_kv
public import Proof.go_etcd_io.bbolt.Bucket__Cursor_kvr
public import Proof.go_etcd_io.bbolt.Bucket__Cursor_kvw
public import Proof.go_etcd_io.bbolt.Bucket__Delete_kv
public import Proof.go_etcd_io.bbolt.Bucket__Put_kv
public import Proof.go_etcd_io.bbolt.Cursor__Next_kv
public import Proof.go_etcd_io.bbolt.Cursor__Seek_kv
public import Proof.go_etcd_io.bbolt.DB__Begin_kv
public import Proof.go_etcd_io.bbolt.DB__Close_kv
public import Proof.go_etcd_io.bbolt.DB__Info_kv
public import Proof.go_etcd_io.bbolt.DB__Stats_kv
public import Proof.go_etcd_io.bbolt.Open_kv
public import Proof.go_etcd_io.bbolt.Tx__Bucket_kvr
public import Proof.go_etcd_io.bbolt.Tx__Bucket_kvw
public import Proof.go_etcd_io.bbolt.Tx__Commit_kv
public import Proof.go_etcd_io.bbolt.Tx__CreateBucketIfNotExists_kv
public import Proof.go_etcd_io.bbolt.Tx__DB_kv
public import Proof.go_etcd_io.bbolt.Tx__Rollback_kv
public import Proof.go_etcd_io.bbolt.Tx__Size_kv
public import Proof.go_etcd_io.bbolt.Tx__Stats_kv
public import Spec.sort.Stable
public import Spec.sort.Sort
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.newBoltLoggerZap
public import Proof.sort.Stable
public import Proof.time.Duration__Seconds
public import Spec.go_etcd_io.bbolt.Cursor__Seek_kv
public import Spec.go_etcd_io.bbolt.Cursor__Next_kv
public import Proof.go_uber_org.zap.Logger__Fatal
public import Proof.go_uber_org.zap.Stack
public import Proof.go_uber_org.zap.Stringer
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStream
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.TxnHandle
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchPos
public import Perennial.Proof.sort.Link
public import Proof.sort.SortAnyLess
public import Perennial.Proof.context.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.sync.Link
public import Proof.github_com.Masterminds.semver.v3.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.pkg.v3.traceutil.Init
public import Proof.go_etcd_io.etcd.server.v3.lease.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Init
public import Proof.go_uber_org.zap.Init
public import Perennial.Golang.Theory.Pkg
public import Code.go_etcd_io.raft.v3.tracker
public import Code.k8s_io.utils.third_party.forked.golang.btree
public import Perennial.Code.cmp
public import Perennial.Code.context
public import Perennial.Code.errors
public import Perennial.Code.fmt
public import Perennial.Code.github_com.goose_lang.primitive
public import Perennial.Code.internal.oserror
public import Perennial.Code.internal.stringslite
public import Perennial.Code.iter
public import Perennial.Code.log
public import Perennial.Code.math
public import Perennial.Code.slices
public import Perennial.Code.sort
public import Perennial.Code.strconv
public import Perennial.Code.strings
public import Perennial.Code.sync
public import Perennial.Code.sync.atomic
public import Perennial.Code.time
public import Perennial.Code.«unsafe»
public import Proof.runtime.Start
public import Perennial.GooseLang.Adequacy
public import Proof.github_com.prometheus.client_golang.prometheus.Registry
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TrivialExt
public import Proof.runtime.Start

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics

/-! ## The program's files -/

namespace mvccfull

open github_com.mit_pdos.etcd_grove.examples.mvccfull

end mvccfull

/-! ## The ghost-state bundle -/

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- The program: `mvccfull`'s initialization, then `Main()`. -/
def mvccfullProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.mvccfull.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.Main) #()

end adequacy

end EtcdGrove
end Perennial

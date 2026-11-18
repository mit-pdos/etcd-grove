/-
`time.Time.IsZero`: the trust boundary (Perennial translates `time` without `Time.IsZero`). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path").
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

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `t.IsZero()`: some boolean (whether `t` is the zero time; `isConnectedSince` only classifies a
connection by it); `t` kept. Unit P1b (2026-10-14). -/
abbrev time.Time.IsZero.spec : Prop :=
  ∀ (p : Loc) (t : _root_.Perennial.time.Time) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.time ∗ p ↦{dq} t }}
    (App (Val (p @!! go.GoType.PointerType _root_.Perennial.time.Time.ty @!! go!"IsZero")) (Val #()))
  {{ (b : Bool), RET #b; p ↦{dq} t }}

end spec

end EtcdGrove
end Perennial

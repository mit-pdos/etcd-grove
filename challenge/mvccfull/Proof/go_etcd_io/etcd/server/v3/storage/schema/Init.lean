/-
Package initialization of `go_etcd_io.etcd.server.v3.storage.schema`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`schemaInit`, `etcdserver/Base.lean`): the `Meta`, `Key`, `Auth`, `AuthUsers` and
`AuthRoles` buckets, as `bucket.go` makes them, the consistent index's two key names (`cindex.go`),
the auth bucket's two key names and the auth backend's `authEnabled`/`authDisabled` values
(`auth.go`; the auth plan's S1, 2026-10-23), and the lessor's `Lease` bucket (leases T3,
2026-10-25). Its initializer allocates and sets those translated variables (with the buckets'
names), initializes its imports and runs its other variables' untranslated initializers, which
the trust-boundary axiom `opaqueInitsOk` says run.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.encoding.binary.Link
public import Proof.go_etcd_io.etcd.api.v3.authpb.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.PkgInit
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Pkg
public import Code.go_etcd_io.raft.v3
public import Code.go_etcd_io.raft.v3.confchange
public import Code.go_etcd_io.raft.v3.raftpb
public import Code.go_etcd_io.raft.v3.tracker
public import Code.google_golang_org.protobuf.proto
public import Code.k8s_io.utils.third_party.forked.golang.btree
public import Perennial.Code.bytes
public import Perennial.Code.cmp
public import Perennial.Code.context
public import Perennial.Code.encoding.binary
public import Perennial.Code.errors
public import Perennial.Code.fmt
public import Perennial.Code.github_com.goose_lang.primitive
public import Perennial.Code.internal.oserror
public import Perennial.Code.internal.stringslite
public import Perennial.Code.io
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
public import Proof.go_etcd_io.etcd.server.v3.auth.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strconv.Base
public import Proof.reflect.PkgInit
public import Perennial.GeneratedProof.bytes
public import Perennial.GeneratedProof.context
public import Perennial.GeneratedProof.crypto.rand
public import Perennial.GeneratedProof.encoding.binary
public import Perennial.GeneratedProof.errors
public import Perennial.GeneratedProof.fmt
public import Perennial.GeneratedProof.cmp
public import Perennial.GeneratedProof.math
public import Perennial.GeneratedProof.slices
public import Perennial.GeneratedProof.strconv
public import Perennial.GeneratedProof.strings
public import Perennial.Golang.Theory
public import Code.go_etcd_io.raft.v3.quorum
public import GeneratedProof.google_golang_org.protobuf.internal.pragma
public import Code.google_golang_org.protobuf.reflect.protoreflect
public import GeneratedProof.google_golang_org.protobuf.internal.impl
public import Code.google_golang_org.protobuf.runtime.protoimpl
public import GeneratedProof.go_etcd_io.raft.v3.tracker
public import Perennial.GeneratedProof.io
public import Perennial.GeneratedProof.log
public import Perennial.GeneratedProof.math.big
public import GooseLang.Ext.Fs.Impl
public import Perennial.GeneratedProof.sync
public import Code.syscall
public import Code.internal.syscall.unix
public import Code.internal.poll
public import Perennial.GeneratedProof.internal.oserror
public import Perennial.GeneratedProof.time
public import Code.io.fs
public import Code.os
public import GeneratedProof.go_etcd_io.raft.v3.chunk2
public import Perennial.Code.reflect
public import Perennial.Proof.context
public import Perennial.Proof.sync
public import Perennial.Proof.fmt
public import Perennial.Proof.slices
public import Perennial.Proof.cmp
public import Proof.errors.NewVar
public import Perennial.Proof.encoding.binary
public import Perennial.Proof.strings
public import Perennial.Proof.math
public import Perennial.Proof.math.bits
public import Perennial.Proof.crypto.rand
public import Perennial.Proof.bytes
public import Perennial.Proof.log
public import Perennial.Proof.io
public import Perennial.Proof.errors
public import Proof.os.PkgInit
public import Perennial.Proof.context.NewErrorString
public import Perennial.Proof.errors.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.sync.Link
public import Proof.internal.poll.PkgInit
public import Proof.internal.syscall.unix.PkgInit
public import Proof.syscall.PkgInit
public import Perennial.Proof.fmt.SprintfModel
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.internal.oserror.Link
public import Perennial.Proof.time.Link
public import Spec.fmt.ErrorOk
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.go_uber_org.zap.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section opaqueInits
namespace go_etcd_io.etcd.server.v3.storage.schema
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.storage.schema`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([«_».init,
        «_».init,
        «_».init,
        alarmBucketName.init,
        clusterBucketName.init,
        membersBucketName.init,
        membersRemovedBucketName.init,
        testBucketName.init,
        Alarm.init,
        Cluster.init,
        Members.init,
        MembersRemoved.init,
        Test.init,
        MetaConfStateName.init,
        ClusterClusterVersionKeyName.init,
        ClusterDowngradeKeyName.init,
        MetaStorageVersionName.init,
        emptyStorageVersion.init,
        schemaChanges.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.storage.schema`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `AllBuckets = []backend.Bucket{Key, Meta, ...}` (`bucket.go`): a slice. -/
axiom AllBuckets_init :
    {{ (True : IProp GF) }} (App (Val AllBuckets.init) (Val #()))
    {{ RET #(); ∃ sl : GoSlice, globalAddr AllBuckets ↦ sl }}

/-- `ScheduledCompactKeyName = []byte("scheduledCompactRev")` (`bucket.go`). -/
axiom ScheduledCompactKeyName_init :
    {{ (True : IProp GF) }} (App (Val ScheduledCompactKeyName.init) (Val #()))
    {{ RET #(); ∃ s : GoSlice, globalAddr ScheduledCompactKeyName ↦ s ∗ s ↦*□ (go!"scheduledCompactRev" : GoString) }}

/-- `FinishedCompactKeyName = []byte("finishedCompactRev")` (`bucket.go`). -/
axiom FinishedCompactKeyName_init :
    {{ (True : IProp GF) }} (App (Val FinishedCompactKeyName.init) (Val #()))
    {{ RET #(); ∃ s : GoSlice, globalAddr FinishedCompactKeyName ↦ s ∗ s ↦*□ (go!"finishedCompactRev" : GoString) }}

end go_etcd_io.etcd.server.v3.storage.schema
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.storage.schema.Assumptions]
variable [_root_.Perennial.errors.Assumptions]

namespace go_etcd_io.etcd.server.v3.storage.schema

end go_etcd_io.etcd.server.v3.storage.schema

end init

end Perennial

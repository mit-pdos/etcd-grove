/-
Package initialization of `go_etcd_io.etcd.client.v3`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`clientv3Init`, `cache/v3/Base.lean`): `noPrefixEnd` (`op.go`, translated:
`[]byte{0}`) and `defaultOptions` (`retry_interceptor.go`, untranslated: `&options{...}` whose
backoff function returns; the trust-boundary axiom `defaultOptions_init`), and its translated
`valCtxCh`, `zeroTime` (`time.Unix(0, 0)`, the trust-boundary axiom `time.Unix.wp_proof`) and
`maxBackoff`, and `LeaseResponseChSize` (`lease.go`, untranslated: `16`; the trust-boundary axiom
`LeaseResponseChSize_init`). Its initializer also runs its other untranslated initializers
(`opaqueInitsOk`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.crypto.tls.Init
public import Proof.go_etcd_io.etcd.api.v3.authpb.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.logutil.Init
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.sync.Link
public import Proof.google_golang_org.grpc.credentials.Init
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
public import Proof.internal.poll.PkgInit
public import Proof.internal.syscall.unix.PkgInit
public import Proof.syscall.PkgInit
public import Perennial.Proof.fmt.SprintfModel
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.internal.oserror.Link
public import Perennial.Proof.time.Link
public import Spec.fmt.ErrorOk
public import Proof.go_uber_org.zap.Init
public import Proof.google_golang_org.grpc.Init
public import Proof.google_golang_org.grpc.codes.Init
public import Proof.google_golang_org.grpc.credentials.Init
public import Proof.google_golang_org.grpc.metadata.Init
public import Proof.net.Init
public import Proof.time.Unix

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
namespace go_etcd_io.etcd.client.v3
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.client.v3`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([ErrNoAvailableEndpoints.init,
        ErrOldCluster.init,
        ErrMutuallyExclusiveCfg.init,
        defaultWaitForReady.init,
        defaultMaxCallSendMsgSize.init,
        defaultMaxCallRecvMsgSize.init,
        defaultStreamMaxRetries.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.client.v3`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `defaultOptions = &options{retryPolicy: nonRepeatable, ..., backoffFunc: backoffLinearWithJitter(50*time.Millisecond, 0.10), ...}` (`retry_interceptor.go`): a pointer to fixed options whose backoff function returns (`jitterUp`'s float arithmetic and `rand.Float64`, which do not panic), with the policy `nonRepeatable` (`W8 1`, `retry.go`'s `iota`; D29). -/
axiom defaultOptions_init :
    {{ (True : IProp GF) }} (App (Val defaultOptions.init) (Val #()))
    {{ RET #(); ∃ (dp : Loc) (ov : options), globalAddr defaultOptions ↦ dp ∗ dp ↦□ ov ∗ go_etcd_io.etcd.cache.v3.backoffOk ov.backoffFunc' ∗ ⌜ov.retryPolicy' = W8 1⌝ }}

/-- `defaultCallOpts = []grpc.CallOption{defaultWaitForReady, defaultMaxCallSendMsgSize, defaultMaxCallRecvMsgSize}` (`options.go`): grpc's `WaitForReady(true)`, `MaxCallSendMsgSize(...)`, `MaxCallRecvMsgSize(...)`, options holding only scalars (`FailFastCallOption`, `MaxSendMsgSizeCallOption`, `MaxRecvMsgSizeCallOption`). -/
axiom defaultCallOpts_init :
    {{ (True : IProp GF) }} (App (Val defaultCallOpts.init) (Val #()))
    {{ RET #(); ∃ (sl : GoSlice) (vs : List GoInterface), globalAddr defaultCallOpts ↦ sl ∗ sl ↦*□ vs ∗ ⌜sl.len = sl.cap ∧ ∀ v ∈ vs, ∃ (t : go.GoType) (x : val), v = interface.mkOk t x ∧ t ∈ [google_golang_org.grpc.StaticMethodCallOption.ty, google_golang_org.grpc.FailFastCallOption.ty, google_golang_org.grpc.MaxSendMsgSizeCallOption.ty, google_golang_org.grpc.MaxRecvMsgSizeCallOption.ty]⌝ }}

/-- `defaultUnaryMaxRetries uint = 100` (`options.go`). -/
axiom defaultUnaryMaxRetries_init :
    {{ (True : IProp GF) }} (App (Val defaultUnaryMaxRetries.init) (Val #()))
    {{ RET #(); ∃ n : w64, globalAddr defaultUnaryMaxRetries ↦ n }}

/-- `defaultBackoffWaitBetween = 25 * time.Millisecond` (`options.go`). -/
axiom defaultBackoffWaitBetween_init :
    {{ (True : IProp GF) }} (App (Val defaultBackoffWaitBetween.init) (Val #()))
    {{ RET #(); ∃ d : time.Duration, globalAddr defaultBackoffWaitBetween ↦ d }}

/-- `defaultBackoffJitterFraction = 0.10` (`options.go`): a float. -/
axiom defaultBackoffJitterFraction_init :
    {{ (True : IProp GF) }} (App (Val defaultBackoffJitterFraction.init) (Val #()))
    {{ RET #(); ∃ f : w64, globalAddr defaultBackoffJitterFraction ↦ f }}

/-- `LeaseResponseChSize = 16` (`lease.go`). -/
axiom LeaseResponseChSize_init :
    {{ (True : IProp GF) }} (App (Val LeaseResponseChSize.init) (Val #()))
    {{ RET #(); globalAddr LeaseResponseChSize ↦ (W64 16 : w64) }}

end go_etcd_io.etcd.client.v3
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.client.v3.Assumptions]

namespace go_etcd_io.etcd.client.v3

end go_etcd_io.etcd.client.v3

end init

end Perennial

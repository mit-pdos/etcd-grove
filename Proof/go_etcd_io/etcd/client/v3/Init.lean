/-
Package initialization of `go_etcd_io.etcd.client.v3`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`clientv3Init`, `cache/v3/Base.lean`): `noPrefixEnd` (`op.go`, translated:
`[]byte{0}`) and `defaultOptions` (`retry_interceptor.go`, untranslated: `&options{...}` whose
backoff function returns; the trust-boundary axiom `defaultOptions_init`). Its initializer also
runs its translated `valCtxCh`, `zeroTime` (`time.Unix(0, 0)`, the trust-boundary axiom
`time.Unix.wp_proof`) and `maxBackoff`, and its other untranslated initializers
(`opaqueInitsOk`).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.crypto.tls.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.logutil.Init
public import Proof.go_etcd_io.etcd.client.v3.credentials.Init
public import Proof.go_etcd_io.etcd.client.v3.internal.endpoint.Init
public import Proof.go_etcd_io.etcd.client.v3.internal.resolver.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_uber_org.zap.Init
public import Proof.google_golang_org.grpc.Init
public import Proof.google_golang_org.grpc.codes.Init
public import Proof.google_golang_org.grpc.credentials.Init
public import Proof.google_golang_org.grpc.credentials.insecure.Init
public import Proof.google_golang_org.grpc.keepalive.Init
public import Proof.google_golang_org.grpc.peer.Init
public import Proof.google_golang_org.grpc.status.Init
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
        LeaseResponseChSize.init,
        defaultWaitForReady.init,
        defaultMaxCallSendMsgSize.init,
        defaultMaxCallRecvMsgSize.init,
        defaultUnaryMaxRetries.init,
        defaultStreamMaxRetries.init,
        defaultBackoffWaitBetween.init,
        defaultBackoffJitterFraction.init,
        defaultCallOpts.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- `defaultOptions = &options{..., backoffFunc: backoffLinearWithJitter(50*time.Millisecond, 0.10), ...}` (`retry_interceptor.go`): a pointer to fixed options whose backoff function returns (`jitterUp`'s float arithmetic and `rand.Float64`, which do not panic). -/
axiom defaultOptions_init :
    {{ (True : IProp GF) }} (App (Val defaultOptions.init) (Val #()))
    {{ RET #(); ∃ (dp : Loc) (ov : options), globalAddr defaultOptions ↦ dp ∗ dp ↦□ ov ∗ go_etcd_io.etcd.cache.v3.backoffOk ov.backoffFunc' }}

end go_etcd_io.etcd.client.v3
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.client.v3.Assumptions]
variable [EtcdGrove.RpctypesEtcdErrorMethods]
variable [_root_.Perennial.context.ErrorStringIsError]
  [_root_.Perennial.context.DeadlineExceededIsError]

namespace go_etcd_io.etcd.client.v3

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.client.v3 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := w64) maxBackoff _ as HmaxBackoff
  wp_apply wp_GlobalAlloc (V := _root_.Perennial.time.Time) zeroTime _ as HzeroTime
  wp_apply wp_GlobalAlloc (V := GoChan) valCtxCh _ as HvalCtxCh
  wp_apply wp_GlobalAlloc (V := GoSlice) noPrefixEnd _ as HnoPrefixEnd
  wp_apply _root_.Perennial.go_etcd_io.etcd.api.v3.mvccpb.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd24⟩
  wp_apply _root_.Perennial.google_golang_org.grpc.peer.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd23⟩
  wp_apply _root_.Perennial.crypto.tls.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd22⟩
  wp_apply _root_.Perennial.google_golang_org.protobuf.proto.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd21⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.client.v3.internal.resolver.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd20⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.client.v3.internal.endpoint.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd19⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.client.v3.credentials.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.client.pkg.v3.logutil.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply _root_.Perennial.google_golang_org.grpc.status.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply _root_.Perennial.google_golang_org.grpc.keepalive.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply _root_.Perennial.google_golang_org.grpc.credentials.insecure.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply _root_.Perennial.google_golang_org.grpc.credentials.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply _root_.Perennial.google_golang_org.grpc.codes.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply _root_.Perennial.go_uber_org.zap.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply _root_.Perennial.errors.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply _root_.Perennial.go_etcd_io.etcd.api.v3.etcdserverpb.wp_initialize' _ Hinit.2.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply _root_.Perennial.google_golang_org.grpc.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply _root_.Perennial.context.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk ErrNoAvailableEndpoints.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrOldCluster.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrMutuallyExclusiveCfg.init (by mem_tac))
  wp_apply (opaqueInitsOk LeaseResponseChSize.init (by mem_tac))
  -- translated initializer of noPrefixEnd))
  wp_apply wp_slice_literal (l := [W8 0])
  isplitr
  · ipureintro; rfl
  iintro %snp ⟨Hsnp, -⟩
  try wp_auto
  wp_apply (opaqueInitsOk defaultWaitForReady.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultMaxCallSendMsgSize.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultMaxCallRecvMsgSize.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultUnaryMaxRetries.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultStreamMaxRetries.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultBackoffWaitBetween.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultBackoffJitterFraction.init (by mem_tac))
  wp_apply (opaqueInitsOk defaultCallOpts.init (by mem_tac))
  wp_apply defaultOptions_init as ⟨%dpdefaultOptions, %ovdefaultOptions, HdefaultOptions, #PdefaultOptions, #SdefaultOptions⟩
  -- translated initializer of valCtxCh))
  -- translated initializer of zeroTime))
  -- translated initializer of maxBackoff))
  wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#His_ch, %Hcap, Hch⟩
  wp_apply EtcdGrove.time.Unix.wp_proof as %zt -
  ipersist Hsnp
  ipersist HnoPrefixEnd
  ipersist HdefaultOptions
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold go_etcd_io.etcd.cache.v3.clientv3Init
  iframe #


end go_etcd_io.etcd.client.v3

end init

end Perennial

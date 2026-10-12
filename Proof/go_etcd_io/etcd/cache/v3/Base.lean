/-
Package initialization instances for `go.etcd.io/etcd/cache/v3` and the packages it
imports (the counterpart of `Proof/go_etcd_io/raft/v3/Base.lean` for the translation of etcd).

`isPkgInit` of a package includes `isPkgInit` of everything it imports, so every package
reachable from the cache's imports needs an instance. The standard-library ones (`bytes`,
`context`, `errors`, `fmt`, `sync`, `time`) are Perennial's; the etcd, k8s, protobuf, grpc and zap
packages are translated names-only or types-only (`Code/{go_etcd_io/etcd,k8s_io,google_golang_org,go_uber_org}/**.toml`), and their
package facts are `True` except where a proof reads a package-level variable: the
cache's `ErrNotReady` (`fmt.Errorf` at init), `ErrUnsupportedRequest` and
`ErrKeyRangeInvalid`, `ErrCacheTimeout` (`errors.New`), and `rpctypes`' `ErrFutureRev` and
`ErrCompacted` each hold a fixed non-nil error (`globalAddr X ↦□ interface.ok e`, as
Perennial's own packages state their globals), and `ErrCompacted.Error()` returns some string
(`errorStringSpec`: it is an `EtcdError`, whose `Error` returns its description), as do the
cache's `ErrKeyRangeInvalid.Error()` and `ErrUnsupportedRequest.Error()`;
`clientv3`'s `noPrefixEnd` points for good to a slice holding the byte `0`. Everything here is an assumption about
package initialization, as in `Proof/go_etcd_io/raft/v3/Base.lean`: nothing proves it from `initialize'`.
-/
module

public import Code.go_etcd_io.etcd.cache.v3
public import GeneratedProof.go_etcd_io.etcd.cache.v3
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.bytes
public import Perennial.Proof.context
public import Perennial.Proof.errors
public import Perennial.Proof.fmt
public import Perennial.Proof.sync
public import Perennial.Proof.time
public import Perennial.Proof.io
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Init

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go_etcd_io.etcd.cache.v3

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

instance protobuf_pragma_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.internal.pragma :=
  define_is_pkg_init iprop(True)
instance protobuf_pragma_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.internal.pragma :=
  build_get_is_pkg_init_wf

instance protobuf_impl_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.internal.impl :=
  define_is_pkg_init iprop(True)
instance protobuf_impl_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.internal.impl :=
  build_get_is_pkg_init_wf

instance protoimpl_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.runtime.protoimpl :=
  define_is_pkg_init iprop(True)
instance protoimpl_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.runtime.protoimpl :=
  build_get_is_pkg_init_wf

instance mvccpb_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb :=
  define_is_pkg_init iprop(True)
instance mvccpb_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb :=
  build_get_is_pkg_init_wf

-- `etcdserverpb` names `membershippb`'s and `authpb`'s messages (2026-10-12: the server's apply
-- package's requests): types and names only, `True` as the others
instance membershippb_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.membershippb :=
  define_is_pkg_init iprop(True)
instance membershippb_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.membershippb :=
  build_get_is_pkg_init_wf

instance authpb_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.authpb :=
  define_is_pkg_init iprop(True)
instance authpb_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.authpb :=
  build_get_is_pkg_init_wf

-- `grpc` (names only; `etcdserverpb`'s streams are its generic interfaces, 2026-10-12: the
-- request path's `RaftKV` names `KV_RangeStreamServer`), before `etcdserverpb`, which imports it
instance grpc_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc :=
  define_is_pkg_init iprop(True)
instance grpc_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc :=
  build_get_is_pkg_init_wf

instance etcdserverpb_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb :=
  define_is_pkg_init iprop(True)
instance etcdserverpb_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb :=
  build_get_is_pkg_init_wf

instance grpc_codes_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.codes :=
  define_is_pkg_init iprop(True)
instance grpc_codes_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.codes :=
  build_get_is_pkg_init_wf

/-- The error value `e`'s `Error()` returns some string (and does not panic). -/
def errorStringSpec (e : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
    WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

instance errorStringSpec_persistent (e : GoInterfaceOk) :
    Persistent (errorStringSpec (GF := GF) e) := by
  unfold errorStringSpec; infer_instance

/-- `rpctypes`' package facts: the two errors the store returns; `ErrCompacted.Error()`
(the watcher's `Compact` puts it in the cancel response) returns some string, and so does
`ErrFutureRev.Error()` (`WatchResponse.Err` returns it; both are `EtcdError`s, whose `Error`
returns their description). -/
abbrev rpctypesInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrFutureRev ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrCompacted ↦□ GoInterface.ok e ∗
      errorStringSpec e) ∗
    □ (∀ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrFutureRev ↦□ GoInterface.ok e -∗
      errorStringSpec e))

instance rpctypes_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes :=
  define_is_pkg_init rpctypesInit
instance rpctypes_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes :=
  build_get_is_pkg_init_wf

-- The names-only target of the alias `grpc/status.Status` (imported by `grpc/status` since
-- `client/v3/leasing` names it).
instance grpc_internal_status_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.internal.status :=
  define_is_pkg_init iprop(True)
instance grpc_internal_status_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.internal.status :=
  build_get_is_pkg_init_wf

instance grpc_status_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.status :=
  define_is_pkg_init iprop(True)
instance grpc_status_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.status :=
  build_get_is_pkg_init_wf

-- The names-only packages of `clientv3.Client`'s field types.

instance grpc_credentials_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.credentials :=
  define_is_pkg_init iprop(True)
instance grpc_credentials_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.credentials :=
  build_get_is_pkg_init_wf

instance clientv3_credentials_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials :=
  define_is_pkg_init iprop(True)
instance clientv3_credentials_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.credentials :=
  build_get_is_pkg_init_wf

instance clientv3_resolver_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver :=
  define_is_pkg_init iprop(True)
instance clientv3_resolver_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.resolver :=
  build_get_is_pkg_init_wf

-- zap imports zapcore (translated since the merge with the server's names-only zap).
instance zapcore_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap.zapcore :=
  define_is_pkg_init iprop(True)
instance zapcore_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap.zapcore :=
  build_get_is_pkg_init_wf

instance zap_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_uber_org.zap :=
  define_is_pkg_init iprop(True)
instance zap_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_uber_org.zap :=
  build_get_is_pkg_init_wf

-- protobuf's `proto` (`clientv3.cloneCompare` calls `proto.Clone`) and `protoreflect`, which
-- it imports (names only).
instance protoreflect_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.reflect.protoreflect :=
  define_is_pkg_init iprop(True)
instance protoreflect_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.reflect.protoreflect :=
  build_get_is_pkg_init_wf

instance proto_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.proto :=
  define_is_pkg_init iprop(True)
instance proto_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.proto :=
  build_get_is_pkg_init_wf

/-- `clientv3`'s package facts: `noPrefixEnd` (`[]byte{0}`, never written), which
`getPrefix` returns for a prefix with no successor. -/
abbrev clientv3Init : IProp GF :=
  iprop(∃ sl : GoSlice, globalAddr go_etcd_io.etcd.client.v3.noPrefixEnd ↦□ sl ∗
    sl ↦*□ [W8 0])

instance clientv3_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3 :=
  define_is_pkg_init clientv3Init
instance clientv3_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3 :=
  build_get_is_pkg_init_wf

-- `k8s.io/utils/third_party/forked/golang/btree`: `Proof/k8s_io/.../btree/Init.lean`.

/-- The cache's package facts: the error variables `ErrNotReady` (the store returns it),
`ErrUnsupportedRequest` (wrapped by `validateGet`/`validateWatch`), `ErrKeyRangeInvalid`
(`validateRange`) and `ErrCacheTimeout` (`waitTillRevision`), each a fixed non-nil error;
`ErrKeyRangeInvalid.Error()` returns some string (`errors.New`'s `*errorString`; `Cache.Watch`
puts it in a cancel response), and so does `ErrUnsupportedRequest.Error()` (`errors.New`'s too;
`fmt.Errorf`'s `%w` of it calls it, `fmt.argsOk`). -/
abbrev cacheInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk, globalAddr ErrNotReady ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrUnsupportedRequest ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrKeyRangeInvalid ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrCacheTimeout ↦□ GoInterface.ok e) ∗
    □ (∀ e : GoInterfaceOk, globalAddr ErrKeyRangeInvalid ↦□ GoInterface.ok e -∗ errorStringSpec e) ∗
    □ (∀ e : GoInterfaceOk, globalAddr ErrUnsupportedRequest ↦□ GoInterface.ok e -∗
      errorStringSpec e))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 :=
  define_is_pkg_init cacheInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 :=
  build_get_is_pkg_init_wf

end init

section errstr
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A non-nil error `err`'s `Error()` returns some string (`errorStringSpec`; persistent): what
`fmt`'s `%v`/`%w` of it needs (`fmt.argsOk`). -/
def errStrOk (err : GoInterface) : IProp GF :=
  iprop(□ ∀ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ → errorStringSpec e)

instance errStrOk_persistent (err : GoInterface) : Persistent (errStrOk (GF := GF) err) := by
  unfold errStrOk; infer_instance

theorem errStrOk_nil : ⊢ errStrOk (GF := GF) GoInterface.nil := by
  unfold errStrOk
  iintro !> %e %h
  cases h

theorem errStrOk_ok (e : GoInterfaceOk) : errorStringSpec (GF := GF) e ⊢ errStrOk (GoInterface.ok e) := by
  unfold errStrOk
  iintro #H !> %e' %h
  cases h
  iexact H

/-- `errStrOk` of `ok e` gives `errorStringSpec e`. -/
theorem errStrOk_elim (e : GoInterfaceOk) : errStrOk (GF := GF) (GoInterface.ok e) ⊢ errorStringSpec e := by
  unfold errStrOk
  iintro #H
  iapply H
  ipureintro; rfl

/-- The `Error()` of an error with a known message (`errors.wp_New`'s) returns some string. -/
theorem errorStringSpec_of_msg (e : GoInterfaceOk) (msg : GoString) :
    iprop(□ ∀ Φ : val → IProp GF, ▷ Φ #msg -∗
      WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }}) ⊢ errorStringSpec e := by
  unfold errorStringSpec
  iintro #H !> %Φ HΦ
  iapply H
  inext
  iapply HΦ

end errstr

end go_etcd_io.etcd.cache.v3

end Perennial

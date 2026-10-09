/-
Package initialization instances for `go.etcd.io/etcd/cache/v3` and the packages it
imports (the counterpart of `Proof/go_etcd_io/raft/v3/Base.lean` for the translation of etcd).

`isPkgInit` of a package includes `isPkgInit` of everything it imports, so every package
reachable from the cache's imports needs an instance. The standard-library ones (`bytes`,
`context`, `errors`, `fmt`, `sync`, `time`) are Perennial's; the etcd, k8s and protobuf
packages are translated names-only or types-only (`Code/{go_etcd_io/etcd,k8s_io,google_golang_org}/**.toml`), and their
package facts are `True` except where a proof reads a package-level variable: the
cache's `ErrNotReady` (`fmt.Errorf` at init), `ErrUnsupportedRequest` and
`ErrKeyRangeInvalid` (`errors.New`), and `rpctypes`' `ErrFutureRev` and
`ErrCompacted` each hold a fixed non-nil error (`globalAddr X ↦□ interface.ok e`, as
Perennial's own packages state their globals), and `ErrCompacted.Error()` returns some string
(`errorStringSpec`: it is an `EtcdError`, whose `Error` returns its description);
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

instance etcdserverpb_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb :=
  define_is_pkg_init iprop(True)
instance etcdserverpb_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb :=
  build_get_is_pkg_init_wf

/-- The error value `e`'s `Error()` returns some string (and does not panic). -/
def errorStringSpec (e : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ str : GoString, Φ #str) -∗
    WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

instance errorStringSpec_persistent (e : GoInterfaceOk) :
    Persistent (errorStringSpec (GF := GF) e) := by
  unfold errorStringSpec; infer_instance

/-- `rpctypes`' package facts: the two errors the store returns; `ErrCompacted.Error()`
(the watcher's `Compact` puts it in the cancel response) returns some string. -/
abbrev rpctypesInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrFutureRev ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk,
      globalAddr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrCompacted ↦□ GoInterface.ok e ∗
      errorStringSpec e))

instance rpctypes_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes :=
  define_is_pkg_init rpctypesInit
instance rpctypes_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes :=
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
`ErrUnsupportedRequest` (wrapped by `validateGet`/`validateWatch`) and `ErrKeyRangeInvalid`
(`validateRange`), each a fixed non-nil error. -/
abbrev cacheInit : IProp GF :=
  iprop((∃ e : GoInterfaceOk, globalAddr ErrNotReady ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrUnsupportedRequest ↦□ GoInterface.ok e) ∗
    (∃ e : GoInterfaceOk, globalAddr ErrKeyRangeInvalid ↦□ GoInterface.ok e))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 :=
  define_is_pkg_init cacheInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 :=
  build_get_is_pkg_init_wf

end init

end go_etcd_io.etcd.cache.v3

end Perennial

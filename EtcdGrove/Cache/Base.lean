/-
Package initialization instances for `go.etcd.io/etcd/cache/v3` and the packages it
imports (the counterpart of `EtcdGrove/Raft/Base.lean` for the `EtcdCache` library).

`isPkgInit` of a package includes `isPkgInit` of everything it imports, so every package
reachable from the cache's imports needs an instance. The standard-library ones (`bytes`,
`context`, `errors`, `fmt`, `sync`, `time`) are Perennial's; the etcd, k8s and protobuf
packages are translated names-only or types-only (`EtcdCache/Code/**.toml`), and no proof
here reads a package-level variable of theirs, so their package facts are `True`. So is
the cache's own: the ring buffer reads no global. Everything here is an assumption about
package initialization, as in `Raft/Base.lean`: nothing proves it from `initialize'`.
-/
import EtcdCache.Code.go_etcd_io.etcd.cache.v3
import EtcdCache.GeneratedProof.go_etcd_io.etcd.cache.v3
import Perennial.Proof.ProofPrelude
import Perennial.Proof.bytes
import Perennial.Proof.context
import Perennial.Proof.errors
import Perennial.Proof.fmt
import Perennial.Proof.sync
import Perennial.Proof.time

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

instance rpctypes_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes :=
  define_is_pkg_init iprop(True)
instance rpctypes_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes :=
  build_get_is_pkg_init_wf

instance clientv3_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3 :=
  define_is_pkg_init iprop(True)
instance clientv3_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3 :=
  build_get_is_pkg_init_wf

instance btree_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree :=
  define_is_pkg_init iprop(True)
instance btree_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree :=
  build_get_is_pkg_init_wf

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 :=
  build_get_is_pkg_init_wf

end init

end go_etcd_io.etcd.cache.v3

end Perennial

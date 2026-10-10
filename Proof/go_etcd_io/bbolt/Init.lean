/-
Package initialization of `go.etcd.io/bbolt` and of the packages it imports that Perennial
gives no initialization predicate (`syscall`, `golang.org/x/sys/unix`, `encoding/hex`, `reflect`,
bbolt's `internal/freelist`; `os`, `hash/fnv` and bbolt's `errors` are in
`internal/common`'s `Init`): being initialized says nothing beyond the imports'
initialization (no proof uses a package variable yet).
-/
module

public import GeneratedProof.go_etcd_io.bbolt
public import Proof.go_etcd_io.bbolt.internal.common.Init
public import Perennial.Proof.sync
public import Perennial.Proof.sync.atomic
public import Perennial.Proof.bytes
public import Perennial.Proof.log
public import Perennial.Proof.math

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance syscall_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.syscall :=
  define_is_pkg_init iprop(True)
instance syscall_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.syscall :=
  build_get_is_pkg_init_wf

instance unix_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.golang_org.x.sys.unix :=
  define_is_pkg_init iprop(True)
instance unix_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.golang_org.x.sys.unix :=
  build_get_is_pkg_init_wf

instance reflect_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.reflect :=
  define_is_pkg_init iprop(True)
instance reflect_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.reflect :=
  build_get_is_pkg_init_wf

instance hex_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.encoding.hex :=
  define_is_pkg_init iprop(True)
instance hex_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.encoding.hex :=
  build_get_is_pkg_init_wf

instance freelist_isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist :=
  define_is_pkg_init iprop(True)
instance freelist_get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist :=
  build_get_is_pkg_init_wf

instance root_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.bbolt :=
  define_is_pkg_init iprop(True)
instance root_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.bbolt :=
  build_get_is_pkg_init_wf

end init

end bbolt
end EtcdGrove
end Perennial

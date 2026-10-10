/-
Package initialization of `go.etcd.io/bbolt/internal/common` and of the packages it
imports that Perennial gives no initialization predicate (`os`, `hash/fnv`, bbolt's
`errors`): being initialized says nothing beyond the imports' initialization.
-/
module

public import GeneratedProof.go_etcd_io.bbolt.internal.common
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.fmt
public import Perennial.Proof.sort_proof.sort_init
public import Perennial.Proof.io
public import Perennial.Proof.runtime
public import Perennial.Proof.time
public import Perennial.Proof.strings
public import Perennial.Proof.unsafe
public import Perennial.Proof.errors

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance os_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.os :=
  define_is_pkg_init iprop(True)
instance os_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.os :=
  build_get_is_pkg_init_wf

instance fnv_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.hash.fnv :=
  define_is_pkg_init iprop(True)
instance fnv_get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.hash.fnv :=
  build_get_is_pkg_init_wf

instance errors_isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.bbolt.errors :=
  define_is_pkg_init iprop(True)
instance errors_get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.bbolt.errors :=
  build_get_is_pkg_init_wf

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.bbolt.internal.common :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.bbolt.internal.common :=
  build_get_is_pkg_init_wf

end init

end bbolt
end EtcdGrove
end Perennial

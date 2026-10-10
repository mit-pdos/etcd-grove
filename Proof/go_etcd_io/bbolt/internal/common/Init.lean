/-
Package initialization of `go.etcd.io/bbolt/internal/common`, as translated (the page-id
helpers with bodies, the rest names only): it initializes `fmt` and `sort` and nothing
else, so being initialized says nothing beyond its imports' initialization.
-/
module

public import GeneratedProof.go_etcd_io.bbolt.internal.common
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.fmt
public import Perennial.Proof.sort_proof.sort_init

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

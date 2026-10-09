/-
Package initialization of `k8s.io/utils/third_party/forked/golang/btree`: it has no
globals, so being initialized says nothing beyond its imports' initialization.
-/
module

public import GeneratedProof.k8s_io.utils.third_party.forked.golang.btree
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.cmp
public import Perennial.Proof.sync
public import Perennial.Proof.sort_proof.sort_init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace btree

open Iris Iris.BI k8s_io.utils.third_party.forked.golang.btree

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.k8s_io.utils.third_party.forked.golang.btree :=
  build_get_is_pkg_init_wf

end init

end btree
end EtcdGrove
end Perennial

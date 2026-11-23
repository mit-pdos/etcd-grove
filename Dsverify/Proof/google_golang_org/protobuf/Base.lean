/-
The package facts of protobuf-go's packages QuePaxa's generated messages import (`True`, names only;
notes/dsv-quepaxa.md): the main tree's (`Proof/go_etcd_io/etcd/cache/v3/Base.lean`,
`Proof/go_etcd_io/raft/v3/Base.lean`) live in modules that import the main tree's `net`, which the
part's `Net/` replaces.
-/
module

public import GeneratedProof.google_golang_org.protobuf.proto
public import GeneratedProof.google_golang_org.protobuf.runtime.protoimpl
public import Perennial.Proof.sync.Base
public import Perennial.Proof.strconv.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace google_golang_org.protobuf

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance internal_pragma_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.internal.pragma :=
  define_is_pkg_init iprop(True)
instance internal_pragma_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.internal.pragma :=
  build_get_is_pkg_init_wf

instance internal_impl_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.internal.impl :=
  define_is_pkg_init iprop(True)
instance internal_impl_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.internal.impl :=
  build_get_is_pkg_init_wf

instance runtime_protoimpl_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.runtime.protoimpl :=
  define_is_pkg_init iprop(True)
instance runtime_protoimpl_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.runtime.protoimpl :=
  build_get_is_pkg_init_wf

instance reflect_protoreflect_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.reflect.protoreflect :=
  define_is_pkg_init iprop(True)
instance reflect_protoreflect_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.reflect.protoreflect :=
  build_get_is_pkg_init_wf

instance proto_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.proto :=
  define_is_pkg_init iprop(True)
instance proto_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.proto :=
  build_get_is_pkg_init_wf

end def_

end google_golang_org.protobuf

end Perennial

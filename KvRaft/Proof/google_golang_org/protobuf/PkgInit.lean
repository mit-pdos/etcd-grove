/-
The `IsPkgInit` instances of the protobuf runtime packages raft's `raftpb` imports (`pragma`,
`impl`, `protoimpl`, `protoreflect`), for the part `KvRaft/` (notes/kvraft-part.md). The part's own:
in the main tree they are in etcd cache's `Base.lean`
(`Proof/go_etcd_io/etcd/cache/v3/Base.lean`), whose imports reach etcd's translation and through
grpc's the main tree's names-only `net`, which the part cannot import beside its own (the net
extension's). The facts are `True`, as there; etc/gen-init.py's initializers of these packages in the
part name this module (its first instance of each package in `KvRaft/Proof/`).
-/
module

public import GeneratedProof.google_golang_org.protobuf.internal.pragma
public import GeneratedProof.google_golang_org.protobuf.internal.impl
public import GeneratedProof.google_golang_org.protobuf.runtime.protoimpl
public import GeneratedProof.google_golang_org.protobuf.reflect.protoreflect
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.sync
public import Perennial.Proof.strconv.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace google_golang_org.protobuf

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

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

instance protoreflect_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.reflect.protoreflect :=
  define_is_pkg_init iprop(True)
instance protoreflect_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.reflect.protoreflect :=
  build_get_is_pkg_init_wf

end init

end google_golang_org.protobuf

end Perennial

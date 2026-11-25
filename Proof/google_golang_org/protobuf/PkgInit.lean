/-
The package facts of protobuf-go's packages this repository translates names only (`internal/pragma`,
`internal/impl`, `runtime/protoimpl`, `reflect/protoreflect`, `proto`): `True`. Raft v3.7's `raftpb` is
protobuf-go v2 (its messages hold `protoimpl`'s state; `raft` and `raftpb` call `proto.Clone`/`Marshal`/
`Unmarshal`/`Size`/`Equal`), etcd's generated messages import them, and so do `Dsverify/`'s QuePaxa
messages. Shared by every tree that imports them (L1, 2026-11-24: until then declared in raft's and
etcd cache's `Base.lean`, and again in `Dsverify/`; `KvNet/` keeps a copy of its own, its
`Proof/google_golang_org/protobuf/PkgInit.lean`).
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

/-
The package-initialization instance of protobuf-go's `proto` for the part `LinuxFs/` (names-only, as
the main tree's in `Proof/go_etcd_io/raft/v3/Base.lean`, which the part cannot import: it imports the
main raft root package, whose names the part's raft root declares too). Its fact is `True`, as there; the
packages it imports likewise.
-/
module

public import GeneratedProof.google_golang_org.protobuf.proto
public import Perennial.Golang.Theory
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace google_golang_org.protobuf.proto

-- the packages `proto` imports (names-only, `True`, as raft's `Base.lean` declares them)
instance internal_pragma_isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.internal.pragma :=
  define_is_pkg_init iprop(True)
instance internal_pragma_get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.internal.pragma :=
  build_get_is_pkg_init_wf
instance reflect_protoreflect_isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.reflect.protoreflect :=
  define_is_pkg_init iprop(True)
instance reflect_protoreflect_get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.reflect.protoreflect :=
  build_get_is_pkg_init_wf
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.proto :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.proto :=
  build_get_is_pkg_init_wf

end google_golang_org.protobuf.proto

end init

end Perennial

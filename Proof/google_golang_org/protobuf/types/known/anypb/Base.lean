/-
protobuf's `anypb` (types only, the type of genproto `status.Status`'s `Details`): its package fact, `True` (its
translated variables are its descriptor's, which no translated code reads).
-/
module

public import GeneratedProof.google_golang_org.protobuf.types.known.anypb
public import Proof.google_golang_org.protobuf.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace google_golang_org.protobuf.types.known.anypb

open Iris Iris.BI

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.protobuf.types.known.anypb :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.protobuf.types.known.anypb :=
  build_get_is_pkg_init_wf

end init

end google_golang_org.protobuf.types.known.anypb
end Perennial

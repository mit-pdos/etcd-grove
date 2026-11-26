/-
genproto's `googleapis/rpc/status` (types only, the message grpc's `internal/status.Status` holds): its package fact, `True` (its
translated variables are its descriptor's, which no translated code reads).
-/
module

public import GeneratedProof.google_golang_org.genproto.googleapis.rpc.status
public import Proof.google_golang_org.protobuf.PkgInit
public import Proof.google_golang_org.protobuf.types.known.anypb.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace google_golang_org.genproto.googleapis.rpc.status

open Iris Iris.BI

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.genproto.googleapis.rpc.status :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.genproto.googleapis.rpc.status :=
  build_get_is_pkg_init_wf

end init

end google_golang_org.genproto.googleapis.rpc.status
end Perennial

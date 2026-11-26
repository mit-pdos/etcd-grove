/-
`status.Error`'s proof linked with its callees' (prove-statuserror, 2026-11-26): for the linking
modules that apply it directly rather than through a `Link.lean` (the generated `rpctypes` package
initializer, `etc/gen-init.py`; the hand-written `grpcdriver` Link).
-/
module

public import Proof.google_golang_org.grpc.status.Error
public import Proof.google_golang_org.grpc.codes.Code__String
public import Proof.google_golang_org.protobuf.proto.EqualStatus
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.strconv.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : Iris.HasLC} {GF : Iris.BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [status_sem : google_golang_org.grpc.status.Assumptions]

theorem status.Error.wp_linked : status.Error.spec (GF := GF) (hG := hG) :=
  status.Error.wp_proof _root_.Perennial.fmt.wp_Sprintf
    (codes.Code.String.wp_proof _root_.Perennial.strconv.wp_FormatInt) proto.EqualStatus.wp_proof

end linked

end EtcdGrove
end Perennial

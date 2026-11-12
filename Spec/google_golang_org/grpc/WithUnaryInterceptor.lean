/-
`grpc.WithUnaryInterceptor(f)` (grpc's `dialoptions.go`, names only; item 5). Lean-first.
-/
module

public import Proof.google_golang_org.grpc.InvDial

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `grpc.WithUnaryInterceptor(f)`: a dial option setting the unary interceptor `f`. -/
abbrev grpc.WithUnaryInterceptor.spec : Prop :=
  ∀ (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.WithUnaryInterceptor)) (Val #f))
  {{ (o : GoInterface), RET #o; ⌜grpcDialOptIs o (.unaryInterceptor f)⌝ }}

end spec

end EtcdGrove
end Perennial

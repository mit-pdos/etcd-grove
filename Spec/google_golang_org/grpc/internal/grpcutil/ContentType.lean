/-
`grpcutil.ContentType(sub)` (grpc's `internal/grpcutil/method.go`): the request's `content-type`.
-/
module

public import Proof.google_golang_org.grpc.HeaderFields

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `ContentType(sub)` returns `contentTypeOf sub`: `application/grpc`, with `+sub` if `sub` is
not empty. -/
abbrev grpcutil.ContentType.spec : Prop :=
  ∀ (sub : GoString),
  {{ (True : IProp GF) }}
    (App (Val (@! google_golang_org.grpc.internal.grpcutil.ContentType)) (Val #sub))
  {{ RET #(grpcHdr.contentTypeOf sub); True }}

end spec

end EtcdGrove
end Perennial

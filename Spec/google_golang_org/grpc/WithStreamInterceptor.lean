/-
`grpc.WithStreamInterceptor(f)` (grpc's `dialoptions.go`, names only; item 5). Lean-first.
-/
module

public import Proof.google_golang_org.grpc.InvDial

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `grpc.WithStreamInterceptor(f)`: a dial option setting the stream interceptor `f`. -/
abbrev grpc.WithStreamInterceptor.spec : Prop :=
  ∀ (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.WithStreamInterceptor)) (Val #f))
  {{ (o : GoInterface), RET #o; ⌜grpcDialOptIs o (.streamInterceptor f)⌝ }}

end spec

end EtcdGrove
end Perennial

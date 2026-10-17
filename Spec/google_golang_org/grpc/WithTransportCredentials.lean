/-
`grpc.WithTransportCredentials(creds)` (grpc's `dialoptions.go`, names only; item 5). Lean-first.
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

/-- `grpc.WithTransportCredentials(creds)`: a dial option setting the transport credentials. -/
abbrev grpc.WithTransportCredentials.spec : Prop :=
  ∀ (creds : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.WithTransportCredentials)) (Val #creds))
  {{ (o : GoInterface), RET #o; ⌜grpcDialOptIs o .transportCreds⌝ }}

end spec

end EtcdGrove
end Perennial

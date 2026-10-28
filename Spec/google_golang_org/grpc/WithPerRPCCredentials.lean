/-
`grpc.WithPerRPCCredentials(creds)` (grpc's `dialoptions.go`, names only; 2026-10-25, the auth
plan's E2d: `clientv3`'s dial of a client with a user name). Lean-first.
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

/-- `grpc.WithPerRPCCredentials(creds)`, any credentials: a dial option adding the per-RPC
credentials `creds` (`.perRPCCreds creds`). -/
abbrev grpc.WithPerRPCCredentials.spec : Prop :=
  ∀ (creds : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.WithPerRPCCredentials)) (Val #creds))
  {{ (o : GoInterface), RET #o; ⌜grpcDialOptIs o (.perRPCCreds creds)⌝ }}

end spec

end EtcdGrove
end Perennial

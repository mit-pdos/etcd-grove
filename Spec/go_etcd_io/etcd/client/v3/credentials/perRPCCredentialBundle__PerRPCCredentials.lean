/-
`(*perRPCCredentialBundle).PerRPCCredentials()` (`client/v3/credentials/credentials.go`; the auth
plan's E2d). Lean-first (no Rocq counterpart); see
`Proof/go_etcd_io/etcd/client/v3/credentials/Defs.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.credentials.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.credentials.Assumptions]

/-- `b.PerRPCCredentials()` on a token bundle's `b` (its `rc`, read-only): some grpc
`PerRPCCredentials`. -/
abbrev credentials.perRPCCredentialBundle.PerRPCCredentials.spec : Prop :=
  ∀ (b rc : Loc),
  {{ (structFieldRef go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle go!"rc" b ↦□ rc :
      IProp GF) }}
    (App (Val (b @!! go.GoType.PointerType
      go_etcd_io.etcd.client.v3.credentials.perRPCCredentialBundle.ty @!! go!"PerRPCCredentials"))
      (Val #()))
  {{ (pc : GoInterface), RET #pc; True }}

end spec

end EtcdGrove
end Perennial

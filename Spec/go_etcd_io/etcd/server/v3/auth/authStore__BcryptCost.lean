/-
`authStore.BcryptCost` (`server/auth/store.go`). Lean-first (no Rocq counterpart); authkv's `Main`
(2026-10-30), for the Auth service's `UserAdd` at a started member (`bcryptCostOk`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- `as.BcryptCost()`: the store's `bcryptCost` field, read-only (`NewAuthStore`'s composite
literal writes it, nothing else does). -/
abbrev auth.authStore.BcryptCost.spec : Prop :=
  ∀ (st : Loc) (c : w64),
  {{ (aF go!"bcryptCost" st ↦□ c : IProp GF) }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"BcryptCost")) (Val #()))
  {{ RET #c; True }}

end spec

end EtcdGrove
end Perennial

/-
`authStore.HasRole` (`server/auth/store.go`): a read of the latest state (the auth plan's S4c, 2026-10-24).
Lean-first (no Rocq counterpart); see `Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` (the
write side's contracts) and `Steps.lean` (the model's steps).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`as.HasRole(user, role)`** with the admin side's authority at `hs` (it takes the batch
transaction's lock, `Lock`'s contract): whether the latest state's user `user` has the role
`role` (false for a user the state lacks); the hook's post `Post` (the lock ran it), the
authority and the write resource kept. -/
abbrev auth.authStore.HasRole.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (Pre Q Post : IProp GF) (user role : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authOwn M hs ∗ authWR st M P f T ∗ mvcc.csContract P f Pre Q Post }}
    (App (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"HasRole")) (Val #user))
      (Val #role))
  {{ (b : Bool), RET #b; Post ∗ authOwn M hs ∗ authWR st M P f T ∗
      ⌜∃ sta : AuthState, histLast M hs sta ∧
        (b = true ↔ ∃ u : User, sta.users !! user = some u ∧ role ∈ u)⌝ }}

end spec

end EtcdGrove
end Perennial

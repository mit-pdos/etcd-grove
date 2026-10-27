/-
`authStore.Recover` (`server/auth/store.go`): the admin side (the auth plan's S4, 2026-10-24).
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

/-- **`as.Recover(be)`** with a new backend `be` (not nil) meeting the read contract in the
store's mode (its states recorded: a premise on the restored backend) and the write contract with
the hook: replaces the store's backend under `beMu` (both halves: the lock's and the admin
side's), reads the new backend's state `sta` (its flag, its revision, its users for the cache)
under its read transaction (the read resource `R`), appends it to the history and sets the flag
and the revision to it; the new state's permissions fit the cache (a premise, as `stepOk`'s).
`Recover` takes no batch lock, so it appends with the whole authority (`authOwnF`, the auth plan's
S4f): the backend swap (D22's restore, `Recover`'s caller) hands it the old backend's lock share
and installs the share of the history with `sta` appended under the new backend's lock, whose
write side is given as the backend states it (`authWBackendOkR`). -/
abbrev auth.authStore.Recover.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (P : IProp GF) (f : val) (T : IProp GF)
    (hs : List AuthState) (be : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authOwnF M hs ∗ authWR st M P f T ∗ tpAdmin st M ∗ R ∗ ⌜be ≠ GoInterface.nil⌝ ∗
      authBackendOk be R M ∗ authWBackendOkR be M P f T ∗
      □ (∀ s : AuthState, authSnap M s -∗ ⌜permsFit s⌝) }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"Recover")) (Val #be))
  {{ RET #(); tpAdmin st M ∗ authWR st M P f T ∗ R ∗ ∃ sta : AuthState, authSnap M sta ∗ authOwnF M (hs ++ [sta]) }}

end spec

end EtcdGrove
end Perennial

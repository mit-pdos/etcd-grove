/-
`authStore.Recover` (`server/auth/store.go`): the admin side (the auth plan's S4, 2026-10-24).
Lean-first (no Rocq counterpart); see `Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean` (the
write side's contracts) and `Steps.lean` (the model's steps).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.auth.TieRes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.auth auth go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`as.Recover(be)`**, one spec over the mode (the auth-on snapshot plan's decision 5 and
candidate (ii), the Freeze of 2026-11-03): the new backend `be` (not nil) with its read contract in
the mode (in `on γa` at its names `γc`, with its write token and whole currency and the apply
thread's share of the old backend's names `γc₀`: `recoverIn`), the store's user's half of the field
`be`, the admin side's halves of the flag and the cache, and the pending authority (`authOwnPM`: in
`on γa` the history caught up to `hs ++ N` beforehand, the latest state still `hs`'s last).
`Recover` swaps the backend under `beMu` (in `on γa` the new names current, the old backend's whole
currency taken out), reads the new backend's state under its read transaction (the read resource
`R`; in `on γa` the latest clause, with the write token: the caught-up history's last `stI`, which
fits the cache, `recoverFit`), stores its revision (the latest state moves to it) and sets the flag
and the cache from it: the authority at `hs ++ N`, with the halves tied to the latest state
(`authOwnT`). It writes nothing, so it takes no write contract and appends no state. (Until then:
the write contract, the whole authority with the lock's share, and an append of the state read.) -/
abbrev auth.authStore.Recover.spec : Prop :=
  ∀ (st : Loc) (R : IProp GF) (M : AuthMode) (hs N : List AuthState) (stI : AuthState)
    (be : GoInterface) (γc₀ γc : AuthBkNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authInv st R M ∗
      authOwnPM M hs N ∗ (∃ be0 : AuthBackend, aF go!"be" st ↦{DFrac.own (1 : Qp).half} be0) ∗
      enabledHalf st M ∗ cacheHalf st M ∗ tpAdmin st M ∗ R ∗ ⌜be ≠ GoInterface.nil⌝ ∗
      authBackendOk be R M γc ∗ recoverIn M γc₀ γc ∗ recoverFit M hs N stI }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"Recover")) (Val #be))
  {{ RET #(); tpAdmin st M ∗ R ∗ aF go!"be" st ↦{DFrac.own (1 : Qp).half} be ∗
      authOwnT st M (hs ++ N) ∗ recoverOut M γc₀ γc }}

end spec

end EtcdGrove
end Perennial

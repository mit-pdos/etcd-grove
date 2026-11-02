# The started member's auth facts (2026-10-30)

authkv's `Main` serves an auth-on member: the Auth service's `UserAdd` takes `bcryptCostOk ast`
(the store's `BcryptCost()` returns), and `SetUp`/`Work` take `□ (srvTLSId s -∗ False)` (the TLS
fallback off). The started member (`common.memberUpOn`, `startServer`'s post) gave neither. Approved
as first drafted, with no critique.

## The approved spec

A getter over a read-only field (`server/auth/store.go`: `return as.bcryptCost`):

```lean
abbrev auth.authStore.BcryptCost.spec : Prop :=
  ∀ (st : Loc) (c : w64),
  {{ (aF go!"bcryptCost" st ↦□ c : IProp GF) }}
    (App (Val (st @!! go.GoType.PointerType authStore.ty @!! go!"BcryptCost")) (Val #()))
  {{ RET #c; True }}
```

and the facts exported along the constructor chain, each where Go establishes it:

- `auth.newAuthStore_on`'s post: `∃ c, aF go!"bcryptCost" stp ↦□ c` (the composite literal writes
  it; nothing writes it again);
- `authStoreKit`'s post: the same under `⌜M.isOn = true⌝`;
- `NewServer.specM`'s post: `srvCfgFieldAddr srv go!"ClientCertAuthEnabled" ↦□
  cfg.ClientCertAuthEnabled'` and `□ (⌜on = true⌝ → srvBcryptField srv)`, where
  `srvBcryptField s := ∃ stl c, (s.authStore ↦□ authIface stl) ∗ (stl.bcryptCost ↦□ c)`;
- `memberUpOn`: `□ (srvTLSId s -∗ False) ∗ srvBcryptField s` (the configuration's `false`, refuted
  by `srvTLSId_false`).

The client's law turns the field into what the served spec takes (`bcryptCostOk_of_field`).

## What it shows

- **Export a fact at the step that makes it true**, and carry it up the chain to the post that
  clients see. Don't add a premise to the client (`Main`) or an axiom.
- **Gate it by the mode** (`⌜on = true⌝ → …`) where only one mode's proof establishes it. Here the
  auth-off store is an axiom, and it stays untouched.
- **Keep an exported restatement unchanged** (`etcdserver/Results.lean`'s `auth_store_new_on`): its
  proof drops the new conjunct, so the trust base's statement does not move.

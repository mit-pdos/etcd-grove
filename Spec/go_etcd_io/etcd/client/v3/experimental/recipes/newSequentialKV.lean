/-
`recipes.newSequentialKV(kv, prefix, val)` (`client/v3/experimental/recipes/key.go`). Lean-first (no Rocq counterpart);
see `InvRecipesClient.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI go_etcd_io.etcd.client.v3.experimental.recipes go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`newSequentialKV(kv, prefix, val)`** (unit 1b), for a prefix `kp` with `pfx <+: kp` (the
priority queue's contracts are at the empty prefix: the key `kp/...` and the bookkeeping key
`__kp` are two disjoint prefixes), knowing etcd has reached `lo`: gets the last key under `kp`,
parses its last `/`-field as a number `n` (`fmt.Sscanf`), and creates `kp/<n + 1, 16 digits>`
together with a put of `__kp`, if `__kp` was not modified since the get (otherwise retries): on
success a fresh `*RemoteKV` for a key under `kp ++ "/"`, absent at `r - 1` and holding `val` at
`r ≥ lo` (`keyCreatedAt`, no lease); a nil pointer with the error otherwise (the get's, `Sscanf`'s on a
last key whose field is not a number, the transaction's). The order of the key (greater than
every key under `kp ++ "/"` before it, given that they all were made this way and number fewer
than `10^16`) is unit 1b's, with Perennial's `Sprintf` model of `%016d` and `Sscanf`'s axiom. -/
abbrev newSequentialKV.spec : Prop :=
  ∀ (kv : GoInterfaceOk) (pfx kp val : GoString) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isRecipesKV (GoInterface.ok kv) pfx ∗ etcdReached lo ∗ ⌜pfx <+: kp⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.newSequentialKV))
      (Val #(GoInterface.ok kv))) (Val #kp)) (Val #val))
  {{ (rk : Loc) (err : GoInterface), RET (PairV #rk #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (key : GoString) (r : w64),
        ownRemoteKV rk ⟨GoInterface.ok kv, key, r, val⟩ ∗ etcdReached r ∗
        keyCreatedAt pfx key val (W64 0) r ∗
        ⌜(kp ++ go!"/") <+: key ∧ sint.Z lo ≤ sint.Z r ∧ sint.Z r < 2 ^ 63 - 1⌝) ∨
      ⌜err ≠ GoInterface.nil ∧ rk = null⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial

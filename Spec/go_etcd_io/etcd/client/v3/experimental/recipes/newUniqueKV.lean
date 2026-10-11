/-
`recipes.newUniqueKV(kv, prefix, val)` (`client/v3/experimental/recipes/key.go`). Lean-first (no Rocq counterpart);
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

/-- **`newUniqueKV(kv, prefix, val)`** (unit 1b), for a prefix `kp` under the prefix `pfx` of
`kv`'s contracts, knowing etcd has reached `lo`: tries `putNewKV` (no lease) on keys
`kp ++ "/" ++ <decimal of time.Now().UnixNano()>` until one is created or the error is not
`ErrKeyExists`: on success a fresh `*RemoteKV` for a key under `kp ++ "/"` created at `r ≥ lo`
(`keyCreatedAt`); a nil pointer with the error otherwise. (The key's shape beyond its prefix,
the decimal, is unit 1b's, with Perennial's `Sprintf` model of `%v` on an integer.) -/
abbrev newUniqueKV.spec : Prop :=
  ∀ (kv : GoInterfaceOk) (pfx kp val : GoString) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isRecipesKV (GoInterface.ok kv) pfx ∗ etcdReached lo ∗ ⌜pfx <+: kp⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.newUniqueKV))
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

/-
`recipes.newUniqueEphemeralKey(s, prefix)` (`client/v3/experimental/recipes/key.go`). Lean-first (no Rocq counterpart);
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

/-- **`newUniqueEphemeralKey(s, prefix)`** (unit 1b): `newUniqueEphemeralKV(s, prefix, "")`. -/
abbrev newUniqueEphemeralKey.spec : Prop :=
  ∀ (s : Loc) (γ : concurrency.SessionNames) (client : Loc) (id : w64) (pfx kp : GoString)
    (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ concurrency.isSession s γ client id ∗ isEtcdRecipesClient client pfx ∗
      etcdReached lo ∗ ⌜pfx <+: kp⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.newUniqueEphemeralKey))
      (Val #s)) (Val #kp))
  {{ (ek : Loc) (err : GoInterface), RET (PairV #ek #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (kv : GoInterfaceOk) (key : GoString) (r : w64),
        clientKVAddr client ↦□ GoInterface.ok kv ∗
        ownEphemeralKV ek ⟨GoInterface.ok kv, key, r, []⟩ ∗
        etcdReached r ∗ keyCreatedAt pfx key [] id r ∗
        ⌜(kp ++ go!"/") <+: key ∧ sint.Z lo ≤ sint.Z r ∧ sint.Z r < 2 ^ 63 - 1⌝) ∨
      ⌜err ≠ GoInterface.nil ∧ ek = null⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial

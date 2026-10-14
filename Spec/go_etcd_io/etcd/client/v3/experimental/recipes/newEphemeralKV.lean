/-
`recipes.newEphemeralKV(s, key, val)` (`client/v3/experimental/recipes/key.go`). Lean-first (no Rocq counterpart);
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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`newEphemeralKV(s, key, val)`**, for a session `s` of the client `client` (with the
lease `id`) and a key under the prefix `pfx` of the client's contracts: `newKV(client.KV, key,
val, s.Lease())`, its `RemoteKV` copied into a fresh `*EphemeralKV` (`ownEphemeralKV`): the key
was created with the session's lease. -/
abbrev newEphemeralKV.spec : Prop :=
  ∀ (s : Loc) (γ : concurrency.SessionNames) (client : Loc) (id : w64) (pfx key val : GoString)
    (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ concurrency.isSession s γ client id ∗ isEtcdRecipesClient client pfx ∗
      etcdReached lo ∗ ⌜pfx <+: key⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.newEphemeralKV))
      (Val #s)) (Val #key)) (Val #val))
  {{ (ek : Loc) (err : GoInterface), RET (PairV #ek #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ (kv : GoInterfaceOk) (r : w64),
        clientKVAddr client ↦□ GoInterface.ok kv ∗
        ownEphemeralKV ek ⟨GoInterface.ok kv, key, r, val⟩ ∗
        etcdReached r ∗ keyCreatedAt pfx key val id r ∗
        ⌜sint.Z lo ≤ sint.Z r ∧ sint.Z r < 2 ^ 63 - 1⌝) ∨
      (concurrency.isPkgErr ErrKeyExists err ∗ ⌜ek = null⌝ ∗ ∃ r : w64, etcdReached r ∗
        etcdPresent pfx key r ∗ ⌜sint.Z lo ≤ sint.Z r⌝) ∨
      (⌜err ≠ GoInterface.nil ∧ ek = null⌝ ∗ clientErrIs err) }}

end spec

end recipes
end EtcdGrove
end Perennial

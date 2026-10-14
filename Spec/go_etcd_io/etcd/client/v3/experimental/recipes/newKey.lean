/-
`recipes.newKey(kv, key, leaseID)` (`client/v3/experimental/recipes/key.go`). Lean-first (no Rocq counterpart);
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

/-- **`newKey(kv, key, leaseID)`**: `newKV(kv, key, "", leaseID)`. -/
abbrev newKey.spec : Prop :=
  ∀ (kv : GoInterfaceOk) (pfx key : GoString) (lease lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ isRecipesKV (GoInterface.ok kv) pfx ∗ etcdReached lo ∗ ⌜pfx <+: key⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.newKey))
      (Val #(GoInterface.ok kv))) (Val #key)) (Val #lease))
  {{ (rk : Loc) (err : GoInterface), RET (PairV #rk #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ r : w64, ownRemoteKV rk ⟨GoInterface.ok kv, key, r, []⟩ ∗
        etcdReached r ∗ keyCreatedAt pfx key [] lease r ∗
        ⌜sint.Z lo ≤ sint.Z r ∧ sint.Z r < 2 ^ 63 - 1⌝) ∨
      (concurrency.isPkgErr ErrKeyExists err ∗ ⌜rk = null⌝ ∗ ∃ r : w64, etcdReached r ∗
        etcdPresent pfx key r ∗ ⌜sint.Z lo ≤ sint.Z r⌝) ∨
      ⌜err ≠ GoInterface.nil ∧ rk = null⌝ }}

end spec

end recipes
end EtcdGrove
end Perennial

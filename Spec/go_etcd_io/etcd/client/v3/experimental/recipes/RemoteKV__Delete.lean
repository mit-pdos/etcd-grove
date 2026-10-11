/-
`recipes.(*RemoteKV).Delete()` (`client/v3/experimental/recipes/key.go`). Lean-first (no Rocq counterpart);
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`rk.Delete()`**, knowing etcd has reached `lo`: with no `KV` (deleted already), `nil`;
otherwise `kv.Delete(context.TODO(), key)` (a key under the prefix `pfx` of `kv`'s contracts),
returning its `deleteResult` (an error, or a revision `r ≥ lo` at which the key is absent:
`deleteTxn_absent`); either way the `kv` field becomes nil. -/
abbrev RemoteKV.Delete.spec : Prop :=
  ∀ (rk : Loc) (st : RemoteKVSt) (pfx : GoString) (lo : w64),
  {{ ownRemoteKV (GF := GF) rk st ∗ isRecipesKV st.kv pfx ∗ etcdReached lo ∗ ⌜pfx <+: st.key⌝ }}
    (App (Val (rk @!! go.GoType.PointerType RemoteKV.ty @!! go!"Delete")) (Val #()))
  {{ (err : GoInterface), RET #err; ownRemoteKV rk { st with kv := GoInterface.nil } ∗
      match st.kv with
      | .nil => iprop(⌜err = GoInterface.nil⌝)
      | .ok _ => deleteResult pfx lo (opDeleteModel st.key []) err }}

end spec

end recipes
end EtcdGrove
end Perennial

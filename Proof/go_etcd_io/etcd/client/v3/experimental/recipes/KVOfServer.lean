/-
**The recipes' client contracts, from the client's specs** (D48, 2026-10-26; until then at the
server's model, the vertical slice's unit V2b). Lean-first, no Rocq counterpart.

`isRecipesKV_of_km`: a `*kv` of etcd's KV `γ.kv` that sends a write at most once (`isKv api γ.kv
false`) meets `isRecipesKV` at the clients' model over the KV state (`client.etcdModelOfKV γ`,
with the adapter's invariant `kmInv γ`), from the four contracts of
`client/v3/KM{Get,Txn,Put}.lean`. `isEtcdRecipesClient_of_km`: a client whose `KV` field is that
`*kv` and whose `Watcher` meets the closable watcher contract (`isEtcdRangeWatcher`, a premise:
the client's Watch spec covers prefix watches only, `notes/STATUS.md`) meets
`isEtcdRecipesClient`.

Premises beyond the specs': a prefix other than `[]` (`isEtcdKVTodo_of_km`'s), `sortNamesOk`
(`grpc`'s status names of the sort enums), `clientErrsIs` (the client's errors as `errors.Is` sees
them), `hAs` (`errors.As` can take `*rpctypes.EtcdError`), and `kmRecipesRest`: that the client saw
revision `1` (`kmReachedAt γ 1`: the contracts' revisions are positive, which the KV state's model
does not say) and the contracts of the requests the specs do not serve (`kmPutRestTodo`: leased
puts and those that need the key's previous value; `kmTxnUncoveredTodo`: serializable read-only
transactions and leased or `IgnoreValue` writes), as the server-model bridge's `kvWritesOk`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesClient
public import Proof.go_etcd_io.etcd.client.v3.KMGet
public import Proof.go_etcd_io.etcd.client.v3.KMTxn
public import Proof.go_etcd_io.etcd.client.v3.KMPut

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **What the recipes' contracts need beyond the specs** (persistent; see the file header). -/
def kmRecipesRest (api : Loc) (γ : client.KMNames) [client.KMWritable γ] (pfx : GoString) : IProp GF :=
  iprop(client.kmReachedAt γ (W64 1) ∗ client.kmPutRestTodo api γ pfx ∗
    client.kmTxnUncoveredTodo api γ)

instance kmRecipesRest_persistent (api : Loc) (γ : client.KMNames) [client.KMWritable γ] (pfx : GoString) :
    Persistent (kmRecipesRest (GF := GF) api γ pfx) := by
  unfold kmRecipesRest; infer_instance

/-- **A client of etcd's KV meets the recipes' `KV` contracts** (`isRecipesKV`) at the adapter's
model: gets, transactions, deletes and puts at `context.TODO()` (see the file header). -/
theorem isRecipesKV_of_km (api : Loc) (γ : client.KMNames) [client.KMWritable γ] (pfx : GoString) (hpfx : pfx ≠ [])
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        client.isKv api γ.kv false ∗ client.kmInv γ ∗ sortNamesOk ∗
        EtcdGrove.client.clientErrsIs ∗ kmRecipesRest api γ pfx ⊢
      isRecipesKV (EM := client.etcdModelOfKV γ) (GoInterface.ok (client.kvIfaceOf api)) pfx := by
  iintro ⟨#Pc, #Hkv, #Hinv, #Hsn, #Hcei, #Hrest⟩
  iunfold kmRecipesRest at Hrest
  icases Hrest with ⟨#H1, #Hput, #Htxn⟩
  unfold isRecipesKV
  simp only
  isplitl []
  · iapply client.isEtcdKVTodo_of_km api γ false pfx hpfx hAs
    iframe #
  isplitl []
  · iapply client.isEtcdTxnKVTodo_of_km api γ pfx hAs
    iframe #
  isplitl []
  · iapply client.isEtcdDeleteKVTodo_of_km api γ pfx hAs
    iframe #
  · iapply client.isEtcdPutKVTodo_of_km api γ pfx hAs
    iframe #

/-- **A client over a `*kv` of etcd's KV meets the recipes' client contract**
(`isEtcdRecipesClient`) at the adapter's model: its `KV` field the `*kv` (`isRecipesKV_of_km`), its
`Watcher` field a watcher meeting the watcher contract (`isEtcdRangeWatcher`, a premise). -/
theorem isEtcdRecipesClient_of_km (cl : Loc) (w : GoInterfaceOk) (api : Loc) (γ : client.KMNames) [client.KMWritable γ]
    (pfx : GoString) (hpfx : pfx ≠ [])
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        clientKVAddr cl ↦□ GoInterface.ok (client.kvIfaceOf api) ∗
        clientWatcherAddr cl ↦□ GoInterface.ok w ∗
        isEtcdRangeWatcher (EM := client.etcdModelOfKV γ) w pfx ∗
        client.isKv api γ.kv false ∗ client.kmInv γ ∗ sortNamesOk ∗
        EtcdGrove.client.clientErrsIs ∗ kmRecipesRest api γ pfx ⊢
      isEtcdRecipesClient (EM := client.etcdModelOfKV γ) cl pfx := by
  iintro ⟨#Pc, #HKV, #HW, #Hw, #Hkv, #Hinv, #Hsn, #Hcei, #Hrest⟩
  ihave #HK := isRecipesKV_of_km api γ pfx hpfx hAs $$ []
  · iframe #
  unfold isEtcdRecipesClient
  iexists (client.kvIfaceOf api), w
  iframe #

end proofs

end recipes
end EtcdGrove
end Perennial

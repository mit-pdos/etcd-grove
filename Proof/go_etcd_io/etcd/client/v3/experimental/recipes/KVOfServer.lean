/-
**The recipes' client contracts, derived at the server's model** (the vertical slice's unit V2b,
2026-10-14). Lean-first, no Rocq counterpart.

`isRecipesKV_of_kv`: a real `*kv` (`kvIfaceOf api`) over a connection to a gRPC server at `addr`
where etcd's `Range`, `Put`, `DeleteRange` and `Txn` are registered (`etcd_kv_served`'s
conclusion) meets `isRecipesKV` in the server's model (`v3rpc.etcdModelOfServer E`), from the four
contracts of `client/v3/ServerKV{Get,Put,Txn}.lean`. `isEtcdRecipesClient_of_kv`: a client whose
`KV` field is that `*kv` and whose `Watcher` meets the watcher contract (a premise: the watch
slice's) meets `isEtcdRecipesClient`.

Premises beyond the registrations and the server's read side: a prefix other than `[]`
(`isEtcdKVTodo_of_kv`'s), `sortNamesOk` (`grpc`'s status names of the sort enums, for a get with a
sort option), `clientErrsIs` (the client's errors as `errors.Is` sees them, for
`txnCommitErrTodo`), and `hAs` (`errors.As` can take `*rpctypes.EtcdError`).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.InvRecipesClient
public import Proof.go_etcd_io.etcd.client.v3.ServerKVTxn

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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **A real `*kv` meets the recipes' `KV` contracts** (`isRecipesKV`) at the server's model:
gets, transactions, deletes and puts at `context.TODO()` (see the file header). -/
theorem isRecipesKV_of_kv (api : Loc) (addr : GoString) (s : Loc) (E : apply.AEnv GF)
    (γw γr : ReadNames) (cid mid : w64) (pfx : GoString) (hpfx : pfx ≠ [])
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isServerRead s E γr ∗
        kvObjAt api addr ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Put" (EtcdGrove.client.etcdPutSpec E γw cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Range" (EtcdGrove.client.etcdRangeSpec E γr cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" (EtcdGrove.client.etcdDeleteSpec E γw cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Txn" (EtcdGrove.client.etcdTxnSpec E γw γr cid mid) ∗
        sortNamesOk ∗ EtcdGrove.client.clientErrsIs ∗
        EtcdGrove.client.srvNonPlainAll γw ⊢
      isRecipesKV (EM := v3rpc.etcdModelOfServer E) (GoInterface.ok (EtcdGrove.client.kvIfaceOf api)) pfx := by
  iintro ⟨#Pc, #Hsrd, #Hkv, #Hp, #Hr, #Hd, #Ht, #Hsn, #Hcei, #Hnp⟩
  unfold isRecipesKV
  simp only
  isplitl []
  · iapply EtcdGrove.client.isEtcdKVTodo_of_kv api addr s E γr cid mid pfx hpfx hAs
    iframe #
  isplitl []
  · iapply EtcdGrove.client.isEtcdTxnKVTodo_of_kv api addr s E γw γr cid mid pfx hAs
    iframe #
  isplitl []
  · iapply EtcdGrove.client.isEtcdDeleteKVTodo_of_kv api addr s E γw γr cid mid pfx hAs
    iframe #
  · iapply EtcdGrove.client.isEtcdPutKVTodo_of_kv api addr s E γw γr cid mid pfx hAs
    iframe #

/-- **A client over a real `*kv` meets the recipes' client contract** (`isEtcdRecipesClient`) at
the server's model: its `KV` field the `*kv` (`isRecipesKV_of_kv`), its `Watcher` field a watcher
meeting the watcher contract (`isEtcdRangeWatcherOpen`, a premise: no watcher is derived yet). -/
theorem isEtcdRecipesClient_of_kv (cl : Loc) (w : GoInterfaceOk) (api : Loc) (addr : GoString)
    (s : Loc) (E : apply.AEnv GF) (γw γr : ReadNames) (cid mid : w64) (pfx : GoString)
    (hpfx : pfx ≠ [])
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isServerRead s E γr ∗
        kvObjAt api addr ∗
        clientKVAddr cl ↦□ GoInterface.ok (EtcdGrove.client.kvIfaceOf api) ∗
        clientWatcherAddr cl ↦□ GoInterface.ok w ∗
        isEtcdRangeWatcherOpen (EM := v3rpc.etcdModelOfServer E) w pfx ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Put" (EtcdGrove.client.etcdPutSpec E γw cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Range" (EtcdGrove.client.etcdRangeSpec E γr cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" (EtcdGrove.client.etcdDeleteSpec E γw cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Txn" (EtcdGrove.client.etcdTxnSpec E γw γr cid mid) ∗
        sortNamesOk ∗ EtcdGrove.client.clientErrsIs ∗
        EtcdGrove.client.srvNonPlainAll γw ⊢
      isEtcdRecipesClient (EM := v3rpc.etcdModelOfServer E) cl pfx := by
  iintro ⟨#Pc, #Hsrd, #Hkv, #HKV, #HW, #Hw, #Hp, #Hr, #Hd, #Ht, #Hsn, #Hcei, #Hnp⟩
  ihave #HK := isRecipesKV_of_kv api addr s E γw γr cid mid pfx hpfx hAs $$ []
  · iframe #
  unfold isEtcdRecipesClient
  iexists (EtcdGrove.client.kvIfaceOf api), w
  iframe #

end proofs

end recipes
end EtcdGrove
end Perennial

/-
**The queue, end to end** (the vertical slice's unit V2b, 2026-10-14; D47, 2026-10-26: over the
client's specs). Lean-first, no Rocq counterpart.

`queue_vertical`: `NewQueue(client, kp)` on a `*Client` whose `KV` is a `*kv` of etcd's KV `γ.kv`
(`isKv`, sending a write at most once) returns a queue whose `Enqueue` and `Dequeue` meet the
recipes' specs at the clients' model over the KV state (`client.etcdModelOfKV γ`, with the
adapter's invariant `kmInv γ`): the composition of `queue_NewQueue`/`queue_Enqueue`/
`queue_Dequeue` with `isEtcdRecipesClient_of_km`. `Dequeue`'s answer is the model's claim
(`dequeuedAt`: the item was under `kp` just before the claim's revision `r`, gone at `r`, and the
claim holds the token of `r`, exclusive: dequeued at most once, `queue_dequeued_once`).

Premises: `isEtcdRecipesClient_of_km`'s (the client's `KV` and `Watcher` fields, the closable
watcher contract `isEtcdRangeWatcher`, unused on `Dequeue`'s get path, needed by its wait path;
`sortNamesOk`, `clientErrsIs`, `hAs`, `kmRecipesRest`) and `kp ≠ []` (`NewQueue`'s).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.KVOfServer
public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes
  go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver


section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [recipes_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **The queue, end to end** (see the file header): `NewQueue(client, kp)` on a client over a
real `*kv` and etcd's server returns a queue whose `Enqueue` meets its spec, and whose `Dequeue`'s
`(v, nil)` is an item `it` with the value `v`, taken by this call in the server's terms
(`queueTaken`), at a revision at least the caller's `lo`, in order (`dequeueOrder`). -/
theorem queue_vertical (cl : Loc) (w : GoInterfaceOk) (api : Loc) (γ : client.KMNames)
    (kp : GoString) (hkp : kp ≠ [])
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        clientKVAddr cl ↦□ GoInterface.ok (EtcdGrove.client.kvIfaceOf api) ∗
        clientWatcherAddr cl ↦□ GoInterface.ok w ∗
        isEtcdRangeWatcher (EM := client.etcdModelOfKV γ) w kp ∗
        client.isKv api γ.kv false ∗ client.kmInv γ ∗ sortNamesOk ∗
        EtcdGrove.client.clientErrsIs ∗ kmRecipesRest api γ kp }}
      (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.NewQueue)) (Val #cl))
        (Val #kp))
    {{ (q : Loc), RET #q;
        (□ ∀ (val : GoString) (lo : w64),
          {{ etcdReached (EM := client.etcdModelOfKV γ) lo }}
            (App (Val (q @!! go.GoType.PointerType Queue.ty @!! go!"Enqueue")) (Val #val))
          {{ (err : GoInterface), RET #err;
              (⌜err = GoInterface.nil⌝ ∗ ∃ (key : GoString) (r : w64),
                etcdReached (EM := client.etcdModelOfKV γ) r ∗
                keyCreatedAt (EM := client.etcdModelOfKV γ) kp key val (W64 0) r ∗
                ⌜(kp ++ go!"/") <+: key ∧ sint.Z lo ≤ sint.Z r⌝) ∨
              ⌜err ≠ GoInterface.nil⌝ }}) ∗
        (□ ∀ (lo : w64),
          {{ context.isClosedchanInit ∗ etcdReached (EM := client.etcdModelOfKV γ) lo ∗
              ⌜0 ≤ sint.Z lo⌝ }}
            (App (Val (q @!! go.GoType.PointerType Queue.ty @!! go!"Dequeue")) (Val #()))
          {{ (v : GoString) (err : GoInterface), RET (PairV #v #err);
              (⌜err = GoInterface.nil⌝ ∗ ∃ (it : EtcdKv) (r : w64),
                dequeuedAt (EM := client.etcdModelOfKV γ) kp kp it r ∗
                dequeueOrder (EM := client.etcdModelOfKV γ) kp kp modRevLe it r ∗
                ⌜v = it.value ∧ sint.Z lo ≤ sint.Z r⌝) ∨
              ⌜err ≠ GoInterface.nil⌝ }}) }} := by
  iintro %Φ ⟨#Pr, #Pc, #HKV, #HW, #Hw, #Hkv, #Hinv, #Hsn, #Hcei, #Hrest⟩ HΦ
  ihave #Hcl := isEtcdRecipesClient_of_km cl w api γ kp hkp hAs $$ []
  · iframe #
  iapply (wp_NewQueue (EM := client.etcdModelOfKV γ) cl kp) $$ []
  · iframe #
    ipureintro; exact hkp
  inext
  iintro %q #Hq
  iapply HΦ
  isplitl []
  · iintro !> %val %lo %Ψ !> #Hlo HΨ
    iapply (Queue.wp_Enqueue (EM := client.etcdModelOfKV γ) q cl kp val lo) $$ []
    · iframe #
    iexact HΨ
  · iintro !> %lo %Ψ !> ⟨#Hci, #Hlo, %Hl0⟩ HΨ
    iapply (Queue.wp_Dequeue (EM := client.etcdModelOfKV γ) q cl kp lo) $$ []
    · iframe #
      ipureintro; exact Hl0
    inext
    iintro %v %err Hout
    iapply HΨ
    icases Hout with (⟨%He, %it, %r, -, Hdq, #Ho, %Hv⟩ | %He)
    · ileft
      isplitl []
      · ipureintro; exact He
      iexists it, r
      iframe Hdq Ho
      ipureintro; exact Hv
    · iright; ipureintro; exact He

end proofs

end recipes
end EtcdGrove
end Perennial

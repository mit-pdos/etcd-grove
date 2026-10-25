/-
**The queue, end to end** (the vertical slice's unit V2b, 2026-10-14). Lean-first, no Rocq
counterpart.

`queue_vertical`: `NewQueue(client, kp)` on a `*Client` whose `KV` is a real `*kv` over a
connection to a gRPC server at `addr` where etcd's `Range`, `Put`, `DeleteRange` and `Txn` are
registered (`etcd_kv_served`'s conclusion) returns a queue whose `Enqueue` and `Dequeue` meet the
recipes' specs in the server's model (`v3rpc.etcdModelOfServer E`): the composition of
`queue_NewQueue`/`queue_Enqueue`/`queue_Dequeue` with `isEtcdRecipesClient_of_kv`. `Dequeue`'s
answer is stated in the server's terms (`queueTaken`): the item it returns was, with its value,
under `kp` in the state of a sealed log (`idxSealed`, unit W-M2b: the clients' model is over
sealed logs; every certified log is one) just before the claim's revision `r` and
gone from it at `r`, and the claim holds the server's token of `r` (`revTok`, exclusive: dequeued
at most once, `queue_vertical_once`); the order (`dequeueOrder`) in the model's terms, which
unfold to the same (`srvEtcdState`).

Premises: `isEtcdRecipesClient_of_kv`'s (the server's read side, the registrations, `kvObjAt`,
the client's `KV` and `Watcher` fields, the closable watcher contract `isEtcdRangeWatcher` (unused on
`Dequeue`'s get path, needed by its wait path; etcd's client watcher meets it, unit W-Q's
`queue_end_to_end_client` in `Results.lean`), `sortNamesOk`, `clientErrsIs`,
`hAs`, the clients' updates `kvWritesOk`: unit W-M3, at the write and the read names, with the
floor of a certified log, which a client holding `etcdKV` in its invariant has, `kvAnyAu_of_inv`)
and `kp ≠ []` (`NewQueue`'s).
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

/-- **A dequeue's claim, in the server's terms**: the token of the claim's revision `r`
(`revTok`, the server's: exclusive); a sealed log in whose state at `r - 1` the item `it`
(under `kp`) was, under `kp`; and a sealed log in whose state at `r` no key-value under `kp`
has `it`'s key. -/
def queueTaken (E : apply.AEnv GF) (kp : GoString) (it : EtcdKv) (r : w64) : IProp GF :=
  iprop(revTok E r ∗
    (∃ log : mvcc.Log, mvcc.idxSealed E.γ.idx log ∗
      ⌜0 ≤ sint.Z (r - W64 1) ∧ sint.Z (r - W64 1) < log.length ∧
        it ∈ txn.underPfx kp (mvcc.stateAt log (sint.Z (r - W64 1)).toNat) ∧ kp <+: it.key⌝) ∗
    (∃ log : mvcc.Log, mvcc.idxSealed E.γ.idx log ∗
      ⌜0 < sint.Z r ∧ sint.Z r < log.length ∧
        ∀ v ∈ txn.underPfx kp (mvcc.stateAt log (sint.Z r).toNat), v.key ≠ it.key⌝))

/-- etcd's state in the server's model is a sealed log's. -/
theorem srvState_sealed (E : apply.AEnv GF) (r : w64) (pfx : GoString) (s : List EtcdKv) :
    etcdState (self := v3rpc.etcdModelOfServer E) r pfx s ⊢
      ∃ log : mvcc.Log, mvcc.idxSealed E.γ.idx log ∗
        ⌜0 ≤ sint.Z r ∧ sint.Z r < log.length ∧
          s = txn.underPfx pfx (mvcc.stateAt log (sint.Z r).toNat)⌝ := by
  rw [v3rpc.etcdModelOfServer_etcdState]
  unfold v3rpc.srvEtcdState v3rpc.srvLog
  iintro ⟨%log, ⟨#H, -⟩, %Hp⟩
  iexists log
  iframe H
  ipureintro; exact Hp

/-- **A dequeue's claim, in the server's terms** (`queueTaken`) from the clients' model's
(`dequeuedAt`). -/
theorem queueTaken_of (E : apply.AEnv GF) (kp : GoString) (it : EtcdKv) (r : w64) :
    dequeuedAt (EM := v3rpc.etcdModelOfServer E) kp kp it r ⊢ queueTaken E kp it r := by
  unfold dequeuedAt
  iintro ⟨#Hd, Htok, ⟨%s, #Hs, %Hit⟩, %Hk⟩
  unfold queueTaken
  rw [v3rpc.etcdModelOfServer_etcdRevToken]
  iframe Htok
  iunfold revKeyDeleted at Hd
  icases Hd with ⟨%s1, %s1', -, #Hs1', %Hp⟩
  ihave ⟨%log, #Hl, %Hlp⟩ := srvState_sealed E _ kp s $$ Hs
  ihave ⟨%log', #Hl', %Hlp'⟩ := srvState_sealed E _ kp s1' $$ Hs1'
  isplitl []
  · iexists log
    iframe Hl
    ipureintro
    obtain ⟨h0, h1, hs⟩ := Hlp
    exact ⟨h0, h1, hs ▸ Hit, Hk⟩
  · iexists log'
    iframe Hl'
    ipureintro
    obtain ⟨h0, h1, hs⟩ := Hlp'
    exact ⟨Hp.1, h1, hs ▸ Hp.2.2⟩

/-- **Dequeued at most once, in the server's terms**: two claims of the same revision are
impossible (the server's token is exclusive). -/
theorem queue_vertical_once (E : apply.AEnv GF) (kp : GoString) (it1 it2 : EtcdKv) (r : w64) :
    queueTaken E kp it1 r ∗ queueTaken E kp it2 r ⊢ (False : IProp GF) := by
  unfold queueTaken
  iintro ⟨⟨H1, -⟩, ⟨H2, -⟩⟩
  iapply revTok_excl E r $$ [$H1 $H2]

/-- **The queue, end to end** (see the file header): `NewQueue(client, kp)` on a client over a
real `*kv` and etcd's server returns a queue whose `Enqueue` meets its spec, and whose `Dequeue`'s
`(v, nil)` is an item `it` with the value `v`, taken by this call in the server's terms
(`queueTaken`), at a revision at least the caller's `lo`, in order (`dequeueOrder`). -/
theorem queue_vertical (cl : Loc) (w : GoInterfaceOk) (api : Loc) (addr : GoString) (s : Loc)
    (E : apply.AEnv GF) (γr : ReadNames) (cid mid : w64) (kp : GoString) (hkp : kp ≠ [])
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isServerRead s E γr ∗
        kvObjAt api [addr] ∗
        clientKVAddr cl ↦□ GoInterface.ok (EtcdGrove.client.kvIfaceOf api) ∗
        clientWatcherAddr cl ↦□ GoInterface.ok w ∗
        isEtcdRangeWatcher (EM := v3rpc.etcdModelOfServer E) w kp ∗
        EtcdGrove.client.kvRegsAt (⟨addr, E, γr, cid, mid⟩ : EtcdGrove.client.SrvAt GF) ∗
        sortNamesOk ∗ EtcdGrove.client.clientErrsIs ∗
        EtcdGrove.client.kvWritesOk api [addr] E γr cid mid }}
      (App (App (Val (@! go_etcd_io.etcd.client.v3.experimental.recipes.NewQueue)) (Val #cl))
        (Val #kp))
    {{ (q : Loc), RET #q;
        (□ ∀ (val : GoString) (lo : w64),
          {{ etcdReached (EM := v3rpc.etcdModelOfServer E) lo }}
            (App (Val (q @!! go.GoType.PointerType Queue.ty @!! go!"Enqueue")) (Val #val))
          {{ (err : GoInterface), RET #err;
              (⌜err = GoInterface.nil⌝ ∗ ∃ (key : GoString) (r : w64),
                etcdReached (EM := v3rpc.etcdModelOfServer E) r ∗
                keyCreatedAt (EM := v3rpc.etcdModelOfServer E) kp key val (W64 0) r ∗
                ⌜(kp ++ go!"/") <+: key ∧ sint.Z lo ≤ sint.Z r⌝) ∨
              ⌜err ≠ GoInterface.nil⌝ }}) ∗
        (□ ∀ (lo : w64),
          {{ context.isClosedchanInit ∗ etcdReached (EM := v3rpc.etcdModelOfServer E) lo ∗
              ⌜0 ≤ sint.Z lo⌝ }}
            (App (Val (q @!! go.GoType.PointerType Queue.ty @!! go!"Dequeue")) (Val #()))
          {{ (v : GoString) (err : GoInterface), RET (PairV #v #err);
              (⌜err = GoInterface.nil⌝ ∗ ∃ (it : EtcdKv) (r : w64), queueTaken E kp it r ∗
                dequeueOrder (EM := v3rpc.etcdModelOfServer E) kp kp modRevLe it r ∗
                ⌜v = it.value ∧ sint.Z lo ≤ sint.Z r⌝) ∨
              ⌜err ≠ GoInterface.nil⌝ }}) }} := by
  iintro %Φ ⟨#Pr, #Pc, #Hsrd, #Hkv, #HKV, #HW, #Hw, #Hreg, #Hsn, #Hcei, #Hnp⟩ HΦ
  ihave #Hregs := EtcdGrove.client.kvRegs_one addr E γr cid mid $$ Hreg
  ihave #Hcl := isEtcdRecipesClient_of_kv cl w api [addr] s E γr cid mid kp hkp hAs $$ []
  · iframe #
  iapply (wp_NewQueue (EM := v3rpc.etcdModelOfServer E) cl kp) $$ []
  · iframe #
    ipureintro; exact hkp
  inext
  iintro %q #Hq
  iapply HΦ
  isplitl []
  · iintro !> %val %lo %Ψ !> #Hlo HΨ
    iapply (Queue.wp_Enqueue (EM := v3rpc.etcdModelOfServer E) q cl kp val lo) $$ []
    · iframe #
    iexact HΨ
  · iintro !> %lo %Ψ !> ⟨#Hci, #Hlo, %Hl0⟩ HΨ
    iapply (Queue.wp_Dequeue (EM := v3rpc.etcdModelOfServer E) q cl kp lo) $$ []
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
      ihave Htk := queueTaken_of E kp it r $$ Hdq
      iframe Htk Ho
      ipureintro; exact Hv
    · iright; ipureintro; exact He

end proofs

end recipes
end EtcdGrove
end Perennial

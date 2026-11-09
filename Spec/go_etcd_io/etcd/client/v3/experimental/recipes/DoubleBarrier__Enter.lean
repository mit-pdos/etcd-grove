/-
`(*DoubleBarrier).Enter()` (`double_barrier.go`): if `count` waiters are there already,
`ErrTooManyClients`; else create a waiter key `key/waiters/<UnixNano>` with the session's lease
(`myKey`), read the waiters again: if this key is past the `count`-th, delete it and
`ErrTooManyClients`; if it is the `count`-th, put `key/ready`; else wait for a put of `key/ready` from
this key's revision.

**Users**: `T/v3_double_barrier_test.go:56,74,135,150,185,194` (enter waits for `count`; an extra
entrant gets `ErrTooManyClients` and leaves no key), `T/v3_closed_watch_test.go:215` (a closed
client: an error, the fixed `issues/recipes-barrier-wait-closed-watch.md`). Snippet:
`recipes/doublebarrier.go`.

**Proof sketch**: `s.Client()` (1d); `enteredClients.spec` (`σ1`, reached from `σ0`): `count` or more:
`ErrTooManyClients` (`init.spec`), nothing created, both updates back. `newUniqueEphemeralKey.spec`
with the caller's creation update `AUc` (its `Q` built to keep `etcdLb` of the state after, with
`etcdLb_init`: the record is a first version, `createdAt`; `R = σc'.kv.rev > σ1.kv.rev ≥ σ0.kv.rev`);
on its error answer or indefinite error, return it, `AUd` back. Store `myKey`. `enteredClients.spec`
again (`σ2`): `count` or more and this key after the `count`-th's creation revision: `myKey.Delete()`
(`RemoteKV.Delete.spec` with `AUd k`), its error ignored, `ErrTooManyClients` with the fact at
`σ2`. The `count`-th: `KV.Put(ready, "")` with an update of `dbPerm γ who key count none` (guard:
`σ2`'s store had `count` waiters), whose commit gives `etcdLb` after it (`readyPutAt` at its revision
`> R`). Fewer, or before the `count`-th: `WaitEvents.spec` on `key/ready` from `R` for `[PUT]`: a put
of the `ready` key at a revision `≥ R`. Every error returned is `recipeErrOk` (`enteredClients`,
`Put`'s `errVal`/`indefCall`, `WaitEvents`'), and not `ErrTooManyClients` (`notRecipeErr`:
`init.spec`'s `recipeErrsOk`, with W0's `callErr_errorsNew` for a `callErr`).

**What it guarantees**: `nil` means this call's waiter key `k` was created at `R` (after `σ0`) by the
caller's update, the first read saw fewer than `count` waiters (at a revision after `σ0`), and
`key/ready` was put at a revision `≥ R`. With no lease expiry (W0's `EnvCfg.leaseExpiry = false`),
waiter keys are deleted only through the callers' delete updates, so a caller counting creations
and deletions in its invariant knows that `count` processes entered before `ready` was put (the
permission's guard), and that `Enter` on `count` live keys never returns `nil` (its first read sees
them). With lease expiry, the same facts hold of revisions.

**Changes**: old spec (`enterResult` over the recipes' client invariant) assumed the keys under the
prefix were the recipes' own. Round 1 used a persistent permission for every write; now one-shot
updates for creating and deleting this process's own key (review 1f-completeness-1, C-1), the
permission only for the `ready` key; the `ErrTooManyClients` arm says whether a key was created.

**Changes (verify-round)**: `ErrTooManyClients` is the value its variable holds (`globalAddr … ↦□ err`), the other errors `notRecipeErr` (A3 F4).

**Margin**: when this call puts `ready` itself, it also knows the `count` waiters at `σ2` (the guard).

**Integration (I1)**: the `ready` put's fact (`readyPutAt`) is gated by the compaction condition `exactFrom σ.kv σ0.kv.rev` (W0's
`EtcdModel.exactFrom`): 1b's `watchStep` gives a response's events (and a progress's emptiness) only
under it, so the facts this call learns from a watch hold only under it; facts learned from a
`Get` would not need it but are stated under the same condition (a caller cannot tell the paths
apart). The weakest condition the watches need: they start at or after that revision.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Recipes

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open go_etcd_io.etcd.client.v3.experimental.recipes

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- **`b.Enter()`**: `nil` only if its waiter key was created (by the caller's update) at `R` after `σ0`, fewer than `count` waiters were there first, and `key/ready` was put at a revision `≥ R`; `ErrTooManyClients` only after `count` waiters at some revision after `σ0`, with the key it created (if any) given to the caller's delete update. -/
def DoubleBarrier.Enter.spec : Prop :=
  ∀ (b : Loc) (γ : Cluster) (who : Principal) (key : GoString) (count id : w64) (my : Option RKSt)
    (σ0 : State) (Qc : State → State → GoString → Resp → IProp GF)
    (Qd : GoString → State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ dbOwn b γ who key count id my ∗ etcdPeek γ ∗ dbPerm γ who key count none ∗
      etcdLb γ σ0 ∗ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (k : GoString) (res : Resp),
             ⌜uniqueKeyIn (waitersPfx key) k ∧ Step who (putNewReq k [] (sint.Z id)) σ σ' res ∧
              ¬ txnCmpFailed res⌝ ∗ etcdState γ σ',
           COMM Qc σ σ' k res }> ∗
      (∀ k : GoString, AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (.deleteRange (delReq k)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Qd k σ σ' res }>) }}
    (App (Val (b @!! go.GoType.PointerType DoubleBarrier.ty @!! go!"Enter")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ my' : Option RKSt, dbOwn b γ who key count id my' ∗
      ((⌜my' = my⌝ ∗ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (k : GoString) (res : Resp),
             ⌜uniqueKeyIn (waitersPfx key) k ∧ Step who (putNewReq k [] (sint.Z id)) σ σ' res ∧
              ¬ txnCmpFailed res⌝ ∗ etcdState γ σ',
           COMM Qc σ σ' k res }> ∗
         (∀ k : GoString, AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (.deleteRange (delReq k)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Qd k σ σ' res }>) ∗
         ((globalAddr go_etcd_io.etcd.client.v3.experimental.recipes.ErrTooManyClients ↦□ err ∗ ∃ (σ : State) (r n : Nat), etcdLb γ σ ∗
             ⌜σ0.kv.rev ≤ r ∧ r ≤ σ.kv.rev ∧
              storeCount (σ.kv.storeAt r) (pfxRange (waitersPfx key)) n ∧ sint.Z count ≤ n⌝) ∨
          (⌜err ≠ GoInterface.nil⌝ ∗ notRecipeErr .tooManyClients err ∗ recipeErrOk err))) ∨
       (⌜my' = my⌝ ∗ (∀ k : GoString, AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (.deleteRange (delReq k)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Qd k σ σ' res }>) ∗
         ((∃ (σ σ' : State) (k : GoString) (e : EtcdErr), Qc σ σ' k (.err e) ∗ ⌜err = errVal e⌝) ∨
          indefCall err)) ∨
       (∃ (σc σc' : State) (st : RKSt) (res : Resp), Qc σc σc' st.key res ∗
         ⌜txnSucceeded res ∧ my' = some st ∧ st.rev = W64 σc'.kv.rev ∧
          uniqueKeyIn (waitersPfx key) st.key⌝ ∗
         ((⌜err = GoInterface.nil ∧ st.live = true⌝ ∗ (∀ k : GoString, AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (.deleteRange (delReq k)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Qd k σ σ' res }>) ∗ ∃ σ : State, etcdLb γ σ ∗
             ⌜σ0.kv.rev < σc'.kv.rev ∧ σc'.kv.rev ≤ σ.kv.rev ∧
              createdAt σ.kv st.key [] (sint.Z id) σc'.kv.rev ∧
              (∃ r1 n, σ0.kv.rev ≤ r1 ∧ r1 < σc'.kv.rev ∧
                 storeCount (σ.kv.storeAt r1) (pfxRange (waitersPfx key)) n ∧ (n : Int) < sint.Z count) ∧
              (EtcdModel.exactFrom σ.kv σ0.kv.rev → ∃ r, σc'.kv.rev ≤ r ∧ r ≤ σ.kv.rev ∧ readyPutAt σ.kv key r)⌝) ∨
          (⌜st.live = false⌝ ∗ globalAddr go_etcd_io.etcd.client.v3.experimental.recipes.ErrTooManyClients ↦□ err ∗
             ((∃ (σ σ' : State) (res' : Resp), Qd st.key σ σ' res') ∨ ∃ e', indefCall e') ∗ ∃ (σ : State) (r n : Nat), etcdLb γ σ ∗
             ⌜σ0.kv.rev ≤ r ∧ r ≤ σ.kv.rev ∧
              storeCount (σ.kv.storeAt r) (pfxRange (waitersPfx key)) n ∧ sint.Z count ≤ n⌝) ∨
          (⌜err ≠ GoInterface.nil ∧ st.live = true⌝ ∗ notRecipeErr .tooManyClients err ∗
             recipeErrOk err ∗ (∀ k : GoString, AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (.deleteRange (delReq k)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Qd k σ σ' res }>))))) }}

end spec

end Recipes
end EtcdGrove
end Perennial

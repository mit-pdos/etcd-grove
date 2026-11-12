/-
`(*DoubleBarrier).Leave()` (`double_barrier.go`): read the waiters; none: done; only this one: delete
`key/ready` and this key; this one the lowest (by mod revision): wait for the highest's delete and
retry; else delete this key, wait for the lowest's delete and retry.

**Users**: `T/v3_double_barrier_test.go:60,92,140,198` (leave waits for every other waiter).
Snippet: `recipes/doublebarrier.go`.

**Proof sketch**: `s.Client()` (1d); `KV.Get` (prefix) with an update of `etcdPeek` (`σg`, reached from
`σ0`): no key: `r = σg.kv.rev`. Else the lowest and highest by mod revision (`keyValueOwn`'s fields),
`myKey.Key()` (`RemoteKV.Key.spec`; `myKey` set, the premise). One key, this one's: `KV.Delete(ready)`
with an update of `dbPerm γ who key count (some st.key)` (guard: `σg`'s waiters are exactly this
key), then `myKey.Delete()` (`RemoteKV.Delete.spec` with the caller's delete update: fired if the
key is live, else back); `r = σg.kv.rev`. Otherwise `WaitEvents.spec` on the highest (or, after
deleting this key with the caller's update, the lowest) from its mod revision (`> 0`: `etcdLb_init`,
a present key's mod revision is at least 2) for `[DELETE]`, then recurse with the same `σ0` (a
deleted `myKey` sends nothing again). Errors: `recipeErrOk`.

**What it guarantees**: `nil` means that at some revision after `σ0` no waiter key but this one's was
there. With no lease expiry and every waiter's key deleted only by its own `Leave` (one-shot
delete updates), that is "every other process called `Leave`".

**Changes**: old spec over the recipes' client invariant; round 1 a persistent permission for the
own key's delete; now the caller's one-shot update (review 1f-completeness-1, C-1), and `dbPerm` for
the `ready` key's delete only, guarded by this key being the only waiter (provability S3).

**Premise**: `myKey` set (`some`): with other waiters present, `b.myKey.Key()` dereferences it
(`nonissues/recipes-dbarrier-leave-without-key.md`; every caller enters first).

**Margin**: none beyond the update dropped on an indefinite delete error.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.experimental.recipes.Api

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

/-- **`b.Leave()`**: `nil` only if, at some revision after `σ0`, no waiter key but possibly this one's was there; this key's delete, if sent, linearized by the caller's update. -/
def DoubleBarrier.Leave.spec : Prop :=
  ∀ (b : Loc) (γ : Cluster) (who : Principal) (key : GoString) (count id : w64) (st : RKSt)
    (σ0 : State) (Qd : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ dbOwn b γ who key count id (some st) ∗ etcdPeek γ ∗ dbPerm γ who key count (some st.key) ∗
      etcdLb γ σ0 ∗
      AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp),
             ⌜Step who (.deleteRange (delReq st.key)) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Qd σ σ' res }> }}
    (App (Val (b @!! go.GoType.PointerType DoubleBarrier.ty @!! go!"Leave")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ∃ st' : RKSt, dbOwn b γ who key count id (some st') ∗ ⌜st'.key = st.key ∧ st'.rev = st.rev⌝ ∗
      ((⌜st'.live = st.live⌝ ∗
         AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
           <{ ∀∀ (σ' : State) (res : Resp),
                ⌜Step who (.deleteRange (delReq st.key)) σ σ' res⌝ ∗ etcdState γ σ',
              COMM Qd σ σ' res }>) ∨
       (⌜st.live = true ∧ st'.live = false⌝ ∗ ((∃ (σ σ' : State) (res : Resp), Qd σ σ' res) ∨ indefCall err))) ∗
      ((⌜err ≠ GoInterface.nil⌝ ∗ recipeErrOk err) ∨
       (⌜err = GoInterface.nil⌝ ∗ ∃ (σ : State) (r : Nat), etcdLb γ σ ∗
         ⌜σ0.kv.rev ≤ r ∧ r ≤ σ.kv.rev ∧
          ∀ k kr, (pfxRange (waitersPfx key)).mem k → σ.kv.storeAt r k = some kr → k = st.key⌝)) }}

end spec

end Recipes
end EtcdGrove
end Perennial

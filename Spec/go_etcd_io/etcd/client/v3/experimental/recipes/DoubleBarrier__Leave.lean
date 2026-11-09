/-
`(*DoubleBarrier).Leave()` (`double_barrier.go`): read the waiters; none: done; only this one: delete
`key/ready` and this key; this one the lowest (by mod revision): wait for the highest's delete and
retry; else delete this key, wait for the lowest's delete and retry.

**Users**: `T/v3_double_barrier_test.go:60,92,140,198` (leave waits for every other waiter).
Snippet: `recipes/doublebarrier.go` (`ReqLeaveAlone`).

**Proof sketch**: `s.Client()` (1d); `KV.Get` (prefix) with an update of `etcdPeek` (`σg`, reached from
`σ0`): no key: `r = σg.kv.rev`. Else the lowest and highest by mod revision (`keyValueOwn`'s fields),
`myKey.Key()` (`RemoteKV.Key.spec`; `myKey` set, the premise). One key, this one's: `KV.Delete(ready)`
with an update of `dbPerm γ who key count id true`'s `ready` case (guard: `σg`'s store had exactly
one waiter), then `myKey.Delete()` (its delete case); `r = σg.kv.rev`, at which only this key was there. Otherwise `WaitEvents.spec` on the
highest (or, after deleting this key, the lowest) from its mod revision for `[DELETE]`, then recurse
(the same `σ0`).

**Changes**: old spec over the recipes' client invariant; now `dbPerm` and the history fact.

**Premise**: `myKey` set (`some`): with other waiters present, `b.myKey.Key()` dereferences it
(`Leave` without a successful `Enter` panics then; every caller enters first).

**Margin**: whether this key was deleted is not said (it is on the "only this one" path, unless it
was deleted through this object before).
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

/-- **`b.Leave()`**: `nil` only if, at some revision after `σ0`, no waiter key but possibly this one's was there. -/
def DoubleBarrier.Leave.spec : Prop :=
  ∀ (b : Loc) (γ : Cluster) (who : Principal) (key : GoString) (count id : w64) (st : RKSt)
    (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ dbOwn b γ who key count id (some st) ∗ etcdPeek γ ∗ dbPerm γ who key count id true ∗
      etcdLb γ σ0 }}
    (App (Val (b @!! go.GoType.PointerType DoubleBarrier.ty @!! go!"Leave")) (Val #()))
  {{ (err : GoInterface), RET #err;
      ∃ st' : RKSt, dbOwn b γ who key count id (some st') ∗ ⌜st'.key = st.key ∧ st'.rev = st.rev⌝ ∗
      (⌜err ≠ GoInterface.nil⌝ ∨
       (⌜err = GoInterface.nil⌝ ∗ ∃ (σ : State) (r : Nat), etcdLb γ σ ∗
         ⌜σ0.kv.rev ≤ r ∧ r ≤ σ.kv.rev ∧
          ∀ k kr, (pfxRange (waitersPfx key)).mem k → σ.kv.storeAt r k = some kr → k = st.key⌝)) }}

end spec

end Recipes
end EtcdGrove
end Perennial

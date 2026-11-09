/-
`(*DoubleBarrier).Enter()` (`double_barrier.go`): if `count` waiters are there already,
`ErrTooManyClients`; else create a waiter key `key/waiters/<UnixNano>` with the session's lease
(`myKey`), read the waiters again: if this key is past the `count`-th, delete it and
`ErrTooManyClients`; if it is the `count`-th, put `key/ready`; else wait for a put of `key/ready` from
this key's revision.

**Users**: `T/v3_double_barrier_test.go:56,74,135,150,185,194` (enter waits for `count`; an extra
entrant gets `ErrTooManyClients`), `T/v3_closed_watch_test.go:215` (a closed client: an error, the
fixed `issues/recipes-barrier-wait-closed-watch.md`). Snippet: `recipes/doublebarrier.go`.

**Proof sketch**: `s.Client()` (1d); `enteredClients.spec` (`σ1`, reached from `σ0`): `count` or more:
`ErrTooManyClients` (`init.spec`), fact at `σ1`. `newUniqueEphemeralKey.spec` with an update made of
`dbPerm γ who key count id false` (its create case; `Q` keeps `etcdLb` of the state after, so `createdAt` and `R > σ1.kv.rev ≥
σ0.kv.rev`); store `myKey`. `enteredClients.spec` again (`σ2`, reached from the creation):
`count` or more and this key after the `count`-th's creation revision: `myKey.Delete()`
(`RemoteKV.Delete.spec`, an update of its delete case), its error ignored, `ErrTooManyClients`
with the fact at `σ2`. The `count`-th: `KV.Put(ready, "")` with an update of its `ready` case
(guard: `σ2`'s store had `count` waiters, `σ2` reached), whose `Q` keeps the `etcdLb` after it
(`readyPutAt` at its revision `> R`). Fewer, or before the `count`-th: `WaitEvents.spec` on
`key/ready` from `R` for `[PUT]`: a put of the `ready` key at a revision `≥ R`.

**What it guarantees**: `nil` means this call's waiter key was created at `R` (after `σ0`), the first
read saw fewer than `count` waiters (at a revision after `σ0`), and the `ready` key was put at a
revision `≥ R`. With `dbPerm` the only writer of `ready`, the caller's invariant knows every such put
followed a revision with `count` waiters.

**Changes**: old spec (`enterResult` over the recipes' client invariant, `dbMyKey`) assumed the keys
under the prefix were the recipes' own; now the caller's permission (`dbPerm`), the history facts.

**Margin**: an error after the key's creation leaves `myKey` set (and the key, unless deleted). When
this call puts `ready` itself, it also knows the `count` waiters at `σ2` (the guard).
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

/-- **`b.Enter()`**: `nil` only if its waiter key was created at `R` after `σ0`, fewer than `count` waiters were there first, and `key/ready` was put at a revision `≥ R`; `ErrTooManyClients` only if `count` waiters were there at some revision after `σ0`. -/
def DoubleBarrier.Enter.spec : Prop :=
  ∀ (b : Loc) (γ : Cluster) (who : Principal) (key : GoString) (count id : w64) (my : Option RKSt)
    (σ0 : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ dbOwn b γ who key count id my ∗ etcdPeek γ ∗ dbPerm γ who key count id false ∗
      etcdLb γ σ0 }}
    (App (Val (b @!! go.GoType.PointerType DoubleBarrier.ty @!! go!"Enter")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ my' : Option RKSt, dbOwn b γ who key count id my' ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (st : RKSt) (σ : State) (R : Nat), etcdLb γ σ ∗
         ⌜my' = some st ∧ sint.Z st.rev = R ∧ σ0.kv.rev < R ∧ R ≤ σ.kv.rev ∧
          uniqueKeyIn (waitersPfx key) st.key ∧ createdAt σ.kv st.key [] (sint.Z id) R ∧
          (∃ r1 n, σ0.kv.rev ≤ r1 ∧ r1 < R ∧
             storeCount (σ.kv.storeAt r1) (pfxRange (waitersPfx key)) n ∧ (n : Int) < sint.Z count) ∧
          ∃ r, R ≤ r ∧ r ≤ σ.kv.rev ∧ readyPutAt σ.kv key r⌝) ∨
       (⌜err = recipeErr .tooManyClients⌝ ∗ ∃ (σ : State) (r n : Nat), etcdLb γ σ ∗
         ⌜σ0.kv.rev ≤ r ∧ r ≤ σ.kv.rev ∧
          storeCount (σ.kv.storeAt r) (pfxRange (waitersPfx key)) n ∧ sint.Z count ≤ n⌝) ∨
       ⌜err ≠ GoInterface.nil ∧ err ≠ recipeErr .tooManyClients⌝) }}

end spec

end Recipes
end EtcdGrove
end Perennial

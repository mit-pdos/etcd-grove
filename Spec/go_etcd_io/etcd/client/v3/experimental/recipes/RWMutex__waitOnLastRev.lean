/-
`(*RWMutex).waitOnLastRev(pfx)` (`rwmutex.go`): read the key under `pfx` with the greatest mod
revision below `myKey`'s revision (`WithLastRev()`, `WithMaxModRev(rev - 1)`); none: done (`true`);
else wait for its delete from `myKey`'s revision (`false`, or the wait's error).

**Users**: `Lock` (`pfx` the mutex's prefix), `RLock` (its writers' prefix). Internal.

**Proof sketch**: `s.Client()` (1d); `myKey.Revision()` (`RemoteKV.Revision.spec`); `KV.Get` with an
update made of `etcdPeek` (`etcdLb γ σg`, the answer at `σg`'s store: with the filter
`maxModRev = R - 1`, the range has no key below `R` iff the answer is empty: `rwHeld`; at `R = 1`
the filter is off, and an empty answer still says no key is there); else `WaitEvents.spec` (`R > 0`)
for `[DELETE]`, its result dropped. Errors: `recipeErrOk`.

**Changes**: old spec over the recipes' client invariant (`rwWaitResult`); now the history fact.

**Premise**: `myKey` set (else a nil dereference), with a revision `R > 0` (one `Lock`/`RLock`
created; `WaitEvents`' premise).

**Margin**: the wait's event is not reported.
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

/-- **`m.waitOnLastRev(pfx)`**: `true` only if no key with prefix `pfx` had a mod revision below `myKey`'s revision at some state reached from it. -/
def RWMutex.waitOnLastRev.spec : Prop :=
  ∀ (m : Loc) (γ : Cluster) (who : Principal) (id : w64) (mpfx pfx : GoString) (st : RKSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.experimental.recipes ∗ rwmOwn m γ who id mpfx (some st) ∗ etcdPeek γ ∗ ⌜0 < sint.Z st.rev⌝ }}
    (App (Val (m @!! go.GoType.PointerType RWMutex.ty @!! go!"waitOnLastRev")) (Val #pfx))
  {{ (done : Bool) (err : GoInterface), RET (PairV #done #err); rwmOwn m γ who id mpfx (some st) ∗
      (⌜done = false ∧ err = GoInterface.nil⌝ ∨ (⌜done = false ∧ err ≠ GoInterface.nil⌝ ∗ recipeErrOk err) ∨
       (⌜done = true ∧ err = GoInterface.nil⌝ ∗ ∃ σ : State, etcdLb γ σ ∗
         ⌜sint.Z st.rev ≤ σ.kv.rev ∧ rwHeld (pfxRange pfx) (sint.Z st.rev).toNat σ.kv.store⌝)) }}

end spec

end Recipes
end EtcdGrove
end Perennial

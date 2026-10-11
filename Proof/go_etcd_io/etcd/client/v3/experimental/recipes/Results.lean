/-
The results of `client/v3/experimental/recipes`, restated at top level, with the trust base of
each printed in the build log (`#print axioms`). Every recipes result rests on the client
bundle's premise that a watch channel is never closed (`isEtcdRecipesClient`, see
`InvRecipesClient.lean`). Each unit's results are in a section of their own.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.experimental.recipes.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace recipes

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.experimental.recipes


/-! ## Unit 3: the RWMutex (`rwmutex.go`) and the double barrier (`double_barrier.go`)

Every function of `rwmutex.go` and `double_barrier.go` has a `Spec`/`Proof` pair and a linked
result (`Link.lean`, generated).

* **`RLock`/`Lock`** (`rwmutex_RLock`, `rwmutex_Lock`): `nil` means the fresh key in `myKey` holds
  the mutex in its role since the revision `R` of `waitOnLastRev`'s last get (`rwHeldAt`: no
  blocking key with a mod revision below the key's creation at `R`); neither checks its own key
  after the wait, so, as `Mutex`'s, the results are about keys present in a state.
* **`RUnlock`/`Unlock`** (`rwmutex_RUnlock`, `rwmutex_Unlock`, `rwmutex_unlock_released`): `nil`
  means the key is absent at some revision at least the caller's.
* **Exclusion** (`rwmutex_write_exclusion`, `rwmutex_read_write_exclusion`): a writer and any other
  holder with a different create revision, and so a reader and a writer, are never both present
  in etcd's state at a revision at or after both of their `rwHeldAt` revisions, **provided the
  holders' keys are never modified** (`keyUnmodified`: the recipe's get filters by mod revision,
  so a key rewritten by another client, which keeps its create revision, stops blocking; the
  recipe itself only creates and deletes its keys). From the history law
  `etcdState_create_persist` alone, as `Mutex`'s exclusion.
* **`Enter`** (`double_barrier_Enter`, `double_barrier_enter_ready`, `double_barrier_enter_count`):
  `nil` means its direct path saw `count` waiters, or its waiting path saw a write of `key/ready`
  at or after its key's creation (`enterReady`); under the protocol's premise on `key/ready`
  (`readyPutsCounted`: every write of it is preceded by `count` waiters), at some revision etcd
  has reached at `Enter`'s return at least `count` keys with the prefix `key/waiters` were
  present. Needs `count > 0` (`NewDoubleBarrier`).
* **`Leave`** (`double_barrier_Leave`, `double_barrier_leave`): `nil`, with the key `Enter` left
  in `myKey` (its record's `KV` not nil), means that key is absent at some revision at least the
  caller's.
-/

section unit3
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.experimental.recipes.Assumptions]

/-- `NewRWMutex(s, prefix)` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/NewRWMutex.lean`). -/
theorem rwmutex_NewRWMutex : NewRWMutex.spec (GF := GF) (hG := hG) := wp_NewRWMutex

/-- `rwm.RLock()` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/RWMutex__RLock.lean`). -/
theorem rwmutex_RLock : RWMutex.RLock.spec (GF := GF) (hG := hG) := RWMutex.wp_RLock

/-- `rwm.Lock()` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/RWMutex__Lock.lean`). -/
theorem rwmutex_Lock : RWMutex.Lock.spec (GF := GF) (hG := hG) := RWMutex.wp_Lock

/-- `rwm.RUnlock()` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/RWMutex__RUnlock.lean`). -/
theorem rwmutex_RUnlock : RWMutex.RUnlock.spec (GF := GF) (hG := hG) := RWMutex.wp_RUnlock

/-- `rwm.Unlock()` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/RWMutex__Unlock.lean`). -/
theorem rwmutex_Unlock : RWMutex.Unlock.spec (GF := GF) (hG := hG) := RWMutex.wp_Unlock

/-- **Unlocking releases**: `RUnlock`/`Unlock` returning `nil` for a key whose record's `KV` is not
nil (what `RLock`/`Lock` leave in `myKey`) means the key is absent at some revision at least
`lo` that etcd has reached. -/
theorem rwmutex_unlock_released (pfx : GoString) (st : RemoteKVSt) (lo : w64)
    (hkv : st.kv ≠ GoInterface.nil) :
    rwUnlockResult (GF := GF) pfx st lo GoInterface.nil ⊢
      ∃ r : w64, etcdReached r ∗ etcdAbsent pfx st.key r ∗ ⌜sint.Z lo ≤ sint.Z r⌝ := by
  unfold rwUnlockResult
  rcases h : st.kv with kv | _
  · simp only
    iintro (%Hne | ⟨-, H⟩)
    · exact absurd rfl Hne
    · iexact H
  · exact absurd h hkv

/-- **Writer exclusion.** A writer `(k1, c1)` holding the RWMutex on `pfx` since `R1` and a holder
`(k2, c2)` in any role since `R2` (what `Lock`/`RLock` return on `nil`), with different create
revisions and keys that are never modified (`keyUnmodified`), are never both present in etcd's
state `s` at a revision `a` at or after `R1` and `R2`. -/
theorem rwmutex_write_exclusion (pfx k1 k2 : GoString) (role : RWRole) (c1 c2 R1 R2 a : w64)
    (s : List EtcdKv) (hne : c1 ≠ c2) (h1 : sint.Z R1 ≤ sint.Z a) (h2 : sint.Z R2 ≤ sint.Z a) :
    rwHeldAt (GF := GF) pfx .write k1 c1 R1 ∗ rwHeldAt pfx role k2 c2 R2 ∗
      keyUnmodified pfx k1 c1 ∗ keyUnmodified pfx k2 c2 ∗ etcdState a pfx s ⊢
      ⌜¬ (EtcdGrove.concurrency.HasKeyAt k1 c1 s ∧ EtcdGrove.concurrency.HasKeyAt k2 c2 s)⌝ :=
  rwHeldAt_write_exclusion pfx k1 k2 role c1 c2 R1 R2 a s hne h1 h2

/-- **Reader-writer exclusion.** A reader `(k1, c1)` since `R1` and a writer `(k2, c2)` since `R2`,
with different create revisions and unmodified keys, are never both present in etcd's state at a
revision at or after `R1` and `R2`. (Two readers may be.) -/
theorem rwmutex_read_write_exclusion (pfx k1 k2 : GoString) (c1 c2 R1 R2 a : w64)
    (s : List EtcdKv) (hne : c1 ≠ c2) (h1 : sint.Z R1 ≤ sint.Z a) (h2 : sint.Z R2 ≤ sint.Z a) :
    rwHeldAt (GF := GF) pfx .read k1 c1 R1 ∗ rwHeldAt pfx .write k2 c2 R2 ∗
      keyUnmodified pfx k1 c1 ∗ keyUnmodified pfx k2 c2 ∗ etcdState a pfx s ⊢
      ⌜¬ (EtcdGrove.concurrency.HasKeyAt k1 c1 s ∧ EtcdGrove.concurrency.HasKeyAt k2 c2 s)⌝ :=
  rwHeldAt_read_write_exclusion pfx k1 k2 c1 c2 R1 R2 a s hne h1 h2

/-- `NewDoubleBarrier(s, key, count)`
(`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/NewDoubleBarrier.lean`). -/
theorem double_barrier_NewDoubleBarrier : NewDoubleBarrier.spec (GF := GF) (hG := hG) :=
  wp_NewDoubleBarrier

/-- `b.Enter()` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/DoubleBarrier__Enter.lean`). -/
theorem double_barrier_Enter : DoubleBarrier.Enter.spec (GF := GF) (hG := hG) :=
  DoubleBarrier.wp_Enter

/-- `b.Leave()` (`Spec/go_etcd_io/etcd/client/v3/experimental/recipes/DoubleBarrier__Leave.lean`). -/
theorem double_barrier_Leave : DoubleBarrier.Leave.spec (GF := GF) (hG := hG) :=
  DoubleBarrier.wp_Leave

/-- **What a successful `Enter` saw** (no premise): `nil` means a fresh key under `key/waiters/`,
and either (the direct path) at least `count` waiters at a revision etcd has reached, or (the
waiting path) a write of `key/ready` at a revision at least the key's creation, which etcd has
reached. -/
theorem double_barrier_enter_ready (b : Loc) (key : GoString) (count id lo : w64) :
    enterResult (GF := GF) b key count id lo GoInterface.nil ⊢
      ∃ st : RemoteKVSt, enterReady (key ++ go!"/") key count st.rev ∗
        ⌜(key ++ go!"/waiters") ++ go!"/" <+: st.key ∧ sint.Z lo ≤ sint.Z st.rev⌝ := by
  unfold enterResult
  iintro (⟨-, %ek, %st, -, -, #H, %Hp⟩ | ⟨Herr, -⟩ | ⟨%Hne, -⟩)
  · iexists st
    iframe H
    ipureintro; exact ⟨Hp.1, Hp.2.1⟩
  · unfold EtcdGrove.concurrency.isPkgErr
    icases Herr with ⟨-, %Hne⟩
    exact absurd rfl Hne
  · exact absurd rfl Hne

/-- **`Enter` returns `nil` only after `count` entrants**: under the protocol's premise on
`key/ready` (`readyPutsCounted`), `Enter` returning `nil` means that at some revision etcd has
reached (so at or before the return) at least `count` keys with the prefix `key/waiters` were
present. -/
theorem double_barrier_enter_count (b : Loc) (key : GoString) (count id lo : w64) :
    enterResult (GF := GF) b key count id lo GoInterface.nil ∗
      readyPutsCounted (key ++ go!"/") key count ⊢
      ∃ R : w64, etcdReached R ∗ waitersSeen (key ++ go!"/") (key ++ go!"/waiters") count R := by
  iintro ⟨H, #Hprem⟩
  ihave ⟨%st, #Hr, -⟩ := double_barrier_enter_ready b key count id lo $$ H
  iapply enterReady_counted (key ++ go!"/") key count st.rev $$ [$Hr $Hprem]

/-- **`Leave` returns `nil` only with the caller's key deleted**: for a key whose record's `KV` is
not nil (what `Enter` leaves in `myKey`), `nil` means the key is absent at some revision at least
`lo` that etcd has reached (deleted by `Leave` itself, or found absent). -/
theorem double_barrier_leave (pfx : GoString) (st : RemoteKVSt) (lo : w64)
    (hkv : st.kv ≠ GoInterface.nil) :
    leaveResult (GF := GF) pfx st lo GoInterface.nil ⊢
      ∃ r : w64, etcdReached r ∗ etcdAbsent pfx st.key r ∗ ⌜sint.Z lo ≤ sint.Z r⌝ := by
  unfold leaveResult
  iintro (⟨-, (H | %H)⟩ | %Hne)
  · iexact H
  · exact absurd H hkv
  · exact absurd rfl Hne

end unit3

end recipes
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.recipes.rwmutex_NewRWMutex
#print axioms Perennial.EtcdGrove.recipes.rwmutex_RLock
#print axioms Perennial.EtcdGrove.recipes.rwmutex_Lock
#print axioms Perennial.EtcdGrove.recipes.rwmutex_RUnlock
#print axioms Perennial.EtcdGrove.recipes.rwmutex_Unlock
#print axioms Perennial.EtcdGrove.recipes.rwmutex_unlock_released
#print axioms Perennial.EtcdGrove.recipes.rwmutex_write_exclusion
#print axioms Perennial.EtcdGrove.recipes.rwmutex_read_write_exclusion
#print axioms Perennial.EtcdGrove.recipes.double_barrier_NewDoubleBarrier
#print axioms Perennial.EtcdGrove.recipes.double_barrier_Enter
#print axioms Perennial.EtcdGrove.recipes.double_barrier_Leave
#print axioms Perennial.EtcdGrove.recipes.double_barrier_enter_ready
#print axioms Perennial.EtcdGrove.recipes.double_barrier_enter_count
#print axioms Perennial.EtcdGrove.recipes.double_barrier_leave

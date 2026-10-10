/-
The exported results of `client/v3/concurrency`'s `Mutex`, restated at top level, with the trust
base of each printed in the build log (`#print axioms`). Every function of `mutex.go` and
`key.go` but `lockerMutex.Lock`/`Unlock` has a `Spec`/`Proof` pair and a linked result
(`Link.lean`, generated).

* **`TryLock`** (`mutex_TryLock`): `nil` means the mutex's key holds the lock at the
  transaction's revision `r` (`lockedAt pfx key rev r`: present with create revision `rev`, no key
  under the prefix created earlier); `ErrLocked` means it deleted its key.
* **`Lock`** (`mutex_Lock`): `nil` means `lockedAt pfx key rev R` at the revision `R` of its last
  `Get` — or that the key was deleted and re-created since `rev` (`keyRecreated`), which `Lock`'s
  last check (the key exists) cannot tell apart (see `Mutex__Lock`'s spec).
* **`Unlock`** (`mutex_Unlock`): `nil` means the key is gone.
* **Mutual exclusion** (`mutex_exclusion`): two holders of the lock on one prefix, with
  different create revisions, are never both present in etcd's state at a revision at or after
  both of their `lockedAt` revisions; and at one revision the holder's create revision is unique
  (`mutex_holder_unique`). Stated over the model facts the specs return; proved from the two
  history laws (`etcdState_revs`, `etcdState_create_persist`) and `etcdState_agree`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency

section results
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `NewMutex(s, pfx)` (`Spec/go_etcd_io/etcd/client/v3/concurrency/NewMutex.lean`). -/
theorem mutex_NewMutex : NewMutex.spec (GF := GF) (hG := hG) := wp_NewMutex

/-- `m.TryLock(ctx)` (`Spec/go_etcd_io/etcd/client/v3/concurrency/Mutex__TryLock.lean`). -/
theorem mutex_TryLock : Mutex.TryLock.spec (GF := GF) (hG := hG) := Mutex.wp_TryLock

/-- `m.Lock(ctx)` (`Spec/go_etcd_io/etcd/client/v3/concurrency/Mutex__Lock.lean`). -/
theorem mutex_Lock : Mutex.Lock.spec (GF := GF) (hG := hG) := Mutex.wp_Lock

/-- `m.Unlock(ctx)` (`Spec/go_etcd_io/etcd/client/v3/concurrency/Mutex__Unlock.lean`). -/
theorem mutex_Unlock : Mutex.Unlock.spec (GF := GF) (hG := hG) := Mutex.wp_Unlock

/-- **Mutual exclusion.** Two holders of the lock on `pfx` (what `TryLock` and `Lock` return on
`nil`), `(k1, c1)` at `R1` and `(k2, c2)` at `R2`, with different create revisions, are never both
present in etcd's state `s` at a revision `a` at or after `R1` and `R2`. (Equal create revisions:
both keys were created by one transaction; a mutex's transaction creates one key, but etcd's model
does not record who wrote a key, so this is not excluded here — see `notes/decisions.md`.) -/
theorem mutex_exclusion (pfx k1 k2 : GoString) (c1 c2 R1 R2 a : w64) (s : List EtcdKv)
    (hne : c1 ≠ c2) (h1 : sint.Z R1 ≤ sint.Z a) (h2 : sint.Z R2 ≤ sint.Z a) :
    lockedAt (GF := GF) pfx k1 c1 R1 ∗ lockedAt pfx k2 c2 R2 ∗ etcdState a pfx s ⊢
      ⌜¬ (HasKeyAt k1 c1 s ∧ HasKeyAt k2 c2 s)⌝ :=
  lockedAt_exclusion pfx k1 k2 c1 c2 R1 R2 a s hne h1 h2

/-- **One holder per revision.** Two ownership facts at the same revision name the same create
revision (etcd has one state per revision, `etcdState_agree`, and both are its minimum). -/
theorem mutex_holder_unique (pfx k1 k2 : GoString) (c1 c2 R : w64) :
    lockedAt (GF := GF) pfx k1 c1 R ∗ lockedAt pfx k2 c2 R ⊢ ⌜c1 = c2⌝ := by
  unfold lockedAt
  iintro ⟨⟨%s1, #Hs1, %Hl1⟩, ⟨%s2, #Hs2, %Hl2⟩⟩
  ihave %Heq := etcdState_agree R pfx s1 s2 $$ [$Hs1 $Hs2]
  subst Heq
  ipureintro
  obtain ⟨⟨v1, hv1, -, hc1⟩, hm1⟩ := Hl1
  obtain ⟨⟨v2, hv2, -, hc2⟩, hm2⟩ := Hl2
  have a := hm1 v2 hv2
  have b := hm2 v1 hv1
  rw [hc2] at a; rw [hc1] at b
  have : sint.Z c1 = sint.Z c2 := by omega
  word

end results

end concurrency
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.concurrency.mutex_TryLock
#print axioms Perennial.EtcdGrove.concurrency.mutex_Lock
#print axioms Perennial.EtcdGrove.concurrency.mutex_Unlock
#print axioms Perennial.EtcdGrove.concurrency.mutex_exclusion
#print axioms Perennial.EtcdGrove.concurrency.mutex_holder_unique

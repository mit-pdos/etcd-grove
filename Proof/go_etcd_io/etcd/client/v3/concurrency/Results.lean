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

`Election` (`election.go`): every function has a `Spec`/`Proof` pair and a linked result.

* **`Campaign`** (`election_Campaign`): `nil` means the campaign's key, with the proposed value at
  some revision, and at the revision `R` of its wait's last `Get` no key under the prefix older than
  it: the leader at `R` (`leaderAt`, the mutex's `lockedAt`) — or its key is gone (`campaignLost`):
  `Campaign` does not check its key after the wait (see its spec, and `notes/STATUS.md`).
* **`Proclaim`**, **`Resign`**, **`Leader`**, **`Observe`** (`election_*`): see their specs.
* **Election exclusion** (`election_exclusion`): two leaders with different create revisions are
  never both present at a revision at or after both of their `leaderAt` revisions (the mutex's).
* **Only the leader proclaims** (`proclaim_only_leader`, pure): a successful `Proclaim`'s step
  (what its spec returns, `proclaimedAt`) for a positive create revision `rev` happened on a state
  where the key had create revision `rev`, and leaves it so with the proclaimed value.
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

/-- `NewElection(s, pfx)` (`Spec/go_etcd_io/etcd/client/v3/concurrency/NewElection.lean`). -/
theorem election_NewElection : NewElection.spec (GF := GF) (hG := hG) := wp_NewElection

/-- `ResumeElection(s, pfx, key, rev)`
(`Spec/go_etcd_io/etcd/client/v3/concurrency/ResumeElection.lean`). -/
theorem election_ResumeElection : ResumeElection.spec (GF := GF) (hG := hG) := wp_ResumeElection

/-- `e.Campaign(ctx, val)` (`Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Campaign.lean`). -/
theorem election_Campaign : Election.Campaign.spec (GF := GF) (hG := hG) := Election.wp_Campaign

/-- `e.Proclaim(ctx, val)` (`Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Proclaim.lean`). -/
theorem election_Proclaim : Election.Proclaim.spec (GF := GF) (hG := hG) := Election.wp_Proclaim

/-- `e.Resign(ctx)` (`Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Resign.lean`). -/
theorem election_Resign : Election.Resign.spec (GF := GF) (hG := hG) := Election.wp_Resign

/-- `e.Leader(ctx)` (`Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Leader.lean`). -/
theorem election_Leader : Election.Leader.spec (GF := GF) (hG := hG) := Election.wp_Leader

/-- `e.Observe(ctx)` (`Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Observe.lean`). -/
theorem election_Observe : Election.Observe.spec (GF := GF) (hG := hG) := Election.wp_Observe

/-- **Election exclusion.** Two leaders on `pfx` (what `Campaign` returns on `nil` in its first
case, or a `Leader`/`Observe` leader fact through `leaderKvAt_leaderAt`), `(k1, c1)` at `R1` and
`(k2, c2)` at `R2`, with different create revisions, are never both present in etcd's state `s` at
a revision `a` at or after `R1` and `R2`. -/
theorem election_exclusion (pfx k1 k2 : GoString) (c1 c2 R1 R2 a : w64) (s : List EtcdKv)
    (hne : c1 ≠ c2) (h1 : sint.Z R1 ≤ sint.Z a) (h2 : sint.Z R2 ≤ sint.Z a) :
    leaderAt (GF := GF) pfx k1 c1 R1 ∗ leaderAt pfx k2 c2 R2 ∗ etcdState a pfx s ⊢
      ⌜¬ (HasKeyAt k1 c1 s ∧ HasKeyAt k2 c2 s)⌝ := by
  unfold leaderAt
  exact lockedAt_exclusion pfx k1 k2 c1 c2 R1 R2 a s hne h1 h2

end results

/-- **Only the leader proclaims** (pure). A successful `Proclaim` of `val` on `key` with the
campaign's create revision `rev > 0` (its spec's `proclaimedAt`: etcd's states `s0` at `r - 1` and
`s` at `r` are a `ProclaimStep`) happened when `key` had create revision `rev` (the guard), and
leaves `key` with create revision `rev` and the value `val`. -/
theorem proclaim_only_leader (key : GoString) (rev : w64) (val : GoString) (lease r : w64)
    (s0 s : List EtcdKv) (h : ProclaimStep key rev val lease r s0 s) (hrev : 0 < sint.Z rev) :
    HasKeyAt key rev s0 ∧ HasKeyValAt key rev val s :=
  proclaimStep_guard key rev val lease r s0 s h hrev

end concurrency
end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.concurrency.mutex_TryLock
#print axioms Perennial.EtcdGrove.concurrency.mutex_Lock
#print axioms Perennial.EtcdGrove.concurrency.mutex_Unlock
#print axioms Perennial.EtcdGrove.concurrency.mutex_exclusion
#print axioms Perennial.EtcdGrove.concurrency.mutex_holder_unique
#print axioms Perennial.EtcdGrove.concurrency.election_Campaign
#print axioms Perennial.EtcdGrove.concurrency.election_Proclaim
#print axioms Perennial.EtcdGrove.concurrency.election_Resign
#print axioms Perennial.EtcdGrove.concurrency.election_Leader
#print axioms Perennial.EtcdGrove.concurrency.election_Observe
#print axioms Perennial.EtcdGrove.concurrency.election_exclusion
#print axioms Perennial.EtcdGrove.concurrency.proclaim_only_leader

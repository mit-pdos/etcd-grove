/-
(hraft_robust R5, R1 §6.1) **What `NewRaft` needs of the crash state it starts from** (`RecOk`, `recRes`):
the vocabulary of `NewRaft.spec`, a defs module (no proof of a function). The fresh case (`freshDur`,
`RecOk_fresh`) is the nocrash kit's: a bootstrapped or empty `InmemStore`, no snapshot.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

open proto gprot

section pure
variable [GooseExts]

/-- The index of the snapshot store's latest snapshot (`0`: none). -/
def latIdx (lat : SnapLatest) : Nat :=
  match lat with
  | none => 0
  | some (m, _) => uint.nat m.Index'

/-- The term of the snapshot store's latest snapshot (`0`: none). -/
def latTerm (lat : SnapLatest) : Nat :=
  match lat with
  | none => 0
  | some (m, _) => uint.nat m.Term'

/-- (hraft_robust R5, R1 §6.1) **The recovered crash state `NewRaft` starts from** (pure part; with
`recRes`, the persistent part):
* no term step pending, the commit index `0` (the atomic is volatile, `dead_vacant`), no install
  pending in the snapshot store (`dead_vacant` drops it);
* the compaction frontier at most the latest snapshot's index (`mainOwnAt`'s `c ≤ lastApplied`,
  `restoreSnapshot` setting `lastApplied` to it);
* `LastIndex` is the largest index stored (`disk.Open` restores it so; a fresh store's `0`/`1`);
* every entry of the protocol log above the latest snapshot is stored (the configuration scan and
  `restoreFromCommittedLogs`' replay read them; `GetLog`'s failure panics in the scan);
* the protocol log's last entry is stored, if the log is not empty (`lastLog`, from `LastIndex` and
  `GetLog`, is `mainOwnAt`'s `(|log|, lastTerm)`; **REQUESTS.md Q1**: false after an ordinary
  install-then-restart, whose store is empty, unless `lastLockInv` keeps the effective last entry);
* (fix 2) a pending discard is of the latest snapshot, and the store holds the protocol log from the
  snapshot's index on (the install's compaction frontier is below it: so `FirstIndex ≤ snapIdx` or the
  store is empty, R1 §6.2's open check), and the log is not empty (REQUESTS.md Q1 again). -/
def RecOk (X : SrvDur) : Prop :=
  X.tp = none ∧ X.s.cidx = 0 ∧ X.pend = none ∧ X.c ≤ latIdx X.lat ∧
  (∀ k e, X.A.m.lookup k = some e → k ≤ uint.nat X.A.hi) ∧
  (X.A.hi = W64 0 ∨ ∃ e, X.A.m.lookup (uint.nat X.A.hi) = some e) ∧
  (∀ k, latIdx X.lat < k → k ≤ X.s.log.length → X.A.m.lookup k = ent X.s.log k) ∧
  (X.s.log.length = 0 ∨ X.A.m.lookup X.s.log.length = ent X.s.log X.s.log.length) ∧
  (∀ d, X.dp = some d → latIdx X.lat = d.x ∧ latTerm X.lat = d.st ∧ 0 < X.s.log.length ∧
    ∀ k, d.x ≤ k → k ≤ X.s.log.length → X.A.m.lookup k = ent X.s.log k)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- (hraft_robust R5, R1 §6.2 "Gap") **The latest snapshot is durable at `i`**, unless its install's
discard is pending (then the discard, fix 2, makes it durable: `installDiscard_core`'s `durLb`).
Persistent. (`latestDur` gives only `durLb ∨ snapFollow`: REQUESTS.md Q3.) -/
def recRes (γ : GNames) (i : SID) (X : SrvDur) : IProp GF :=
  match X.lat with
  | none => iprop(True)
  | some (m, _) => iprop(durLb γ i (uint.nat m.Index') ∨ ⌜∃ d, X.dp = some d⌝)

instance recRes_persistent γ i X : Persistent (recRes (GF := GF) γ i X) := by
  unfold recRes; rcases X.lat with _ | ⟨_, _⟩ <;> infer_instance

end defs

section fresh
variable [GooseExts]

/-- (hraft_robust R5) **A fresh server's crash state** (the nocrash kit's, and a restarted kit's first
boot): the genesis state `initSrv` over the bootstrapped store (`[g]` at index 1 for a bootstrap voter,
empty otherwise), the stable store `sst`, no snapshot, nothing pending. -/
def freshDur (cv : List w8 → List SID) (g : Entry) (i : SID) (sst : StableAbs) : SrvDur :=
  ⟨initSrv cv g i, LogAbs.empty.store 1 (initSrv cv g i).log, 1, 0, sst, none, none, none, none⟩

/-- The bootstrapped log store's map: the genesis at index 1. -/
theorem genesisStore_lookup (g : Entry) (k : Nat) :
    (LogAbs.empty.store 1 [g]).m.lookup k = if k = 1 then some g else none := by
  simp only [LogAbs.store, LogAbs.empty, LogAbs.ins, GMap.lookup_insert_eq_iff]
  by_cases h : k = 1
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h]; rfl

theorem RecOk_fresh (cv : List w8 → List SID) (g : Entry) (i : SID) (sst : StableAbs) :
    RecOk (freshDur cv g i sst) := by
  unfold RecOk freshDur latIdx
  by_cases hm : i ∈ cv g.data
  · simp only [initSrv, hm, ite_true]
    have hhi : (LogAbs.empty.store 1 [g]).hi = W64 1 := by simp [LogAbs.store, LogAbs.empty]
    refine ⟨trivial, trivial, trivial, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩
    · intro k e h
      rw [genesisStore_lookup] at h
      rw [hhi]
      split at h
      · subst_vars; simp
      · cases h
    · right; refine ⟨g, ?_⟩; rw [hhi, genesisStore_lookup]; simp
    · intro k _ hk
      have : k = 1 := by simp at hk; omega
      subst this; rw [genesisStore_lookup]; simp [ent]
    · right; rw [genesisStore_lookup]; simp [ent]
    · intro d h; cases h
  · simp only [initSrv, hm, ite_false]
    refine ⟨trivial, trivial, trivial, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩
    · intro k e h; simp [LogAbs.store, LogAbs.empty, LogAbs.ins] at h
    · left; rfl
    · intro k _ hk; simp at hk; omega
    · left; rfl
    · intro d h; cases h

end fresh

end github_com.hashicorp.raft

end Perennial

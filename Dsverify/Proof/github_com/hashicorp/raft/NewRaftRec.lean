/-
(hraft_robust R5, R1 §6.1) **What `NewRaft` needs of the crash state it starts from** (`RecOk`):
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

/-- (hraft_robust R5, R1 §6.1) **The recovered crash state `NewRaft` starts from** (pure; the rest is
`durBody`'s, which `NewRaft` reads at its invariant openings, the stores' state pinned by the boot pin):
* no term step pending, the commit index `0` (the atomic is volatile, `dead_vacant`), no install
  pending in the snapshot store (`dead_vacant` drops it);
* the compaction frontier at most the latest snapshot's index (`mainOwnAt`'s `c ≤ lastApplied`,
  `restoreSnapshot` setting `lastApplied` to it);
* `LastIndex` is the largest index stored (`disk.Open` restores it so; a fresh store's `0`/`1`);
* every entry of the protocol log above the latest snapshot is stored (the configuration scan and
  `restoreFromCommittedLogs`' replay read them; `GetLog`'s failure panics in the scan): from the vacant
  state's `logOk` with `lo ≤ c + 1 ≤ latIdx + 1`;
* (fix 2) a pending discard is of the latest snapshot; with none pending, the store holds no entry at or below
  the latest's index unless it holds the latest's (compaction deletes a prefix: else fix 2 would discard a log
  the protocol keeps). -/
def RecOk (X : SrvDur) : Prop :=
  X.tp = none ∧ X.s.cidx = 0 ∧ X.pend = none ∧ X.c ≤ latIdx X.lat ∧
  (∀ k e, X.A.m.lookup k = some e → k ≤ uint.nat X.A.hi) ∧
  (X.A.hi = W64 0 ∨ ∃ e, X.A.m.lookup (uint.nat X.A.hi) = some e) ∧
  (∀ k, latIdx X.lat < k → k ≤ X.s.log.length → X.A.m.lookup k = ent X.s.log k) ∧
  (∀ d, X.dp = some d → latIdx X.lat = d.x ∧ latTerm X.lat = d.st) ∧
  (X.dp = none → ∀ k e, X.A.m.lookup k = some e → k ≤ latIdx X.lat →
    ∃ e', X.A.m.lookup (latIdx X.lat) = some e')

/-- (hraft_robust R5) **`LastIndex` against the protocol log** at boot: at most the log's length (every stored
entry is a log entry), and the length itself when the log goes past the latest snapshot `x` (its last entry is
stored). -/
theorem rec_hi (A : LogAbs) (L : RLog) (x : Nat)
    (h1 : ∀ k e, A.m.lookup k = some e → ent L k = some e)
    (hhi1 : ∀ k e, A.m.lookup k = some e → k ≤ uint.nat A.hi)
    (hhi2 : A.hi = W64 0 ∨ ∃ e, A.m.lookup (uint.nat A.hi) = some e)
    (habove : ∀ k, x < k → k ≤ L.length → A.m.lookup k = ent L k) :
    uint.nat A.hi ≤ L.length ∧ (x < L.length → uint.nat A.hi = L.length) := by
  have hle : uint.nat A.hi ≤ L.length := by
    rcases hhi2 with h | ⟨e, he⟩
    · rw [h]; simp
    · exact (proto.ent_le_length (h1 _ _ he)).2
  refine ⟨hle, fun hx => ?_⟩
  obtain ⟨e, he⟩ := proto.ent_isSome L L.length (by omega) (Nat.le_refl _)
  have hs : A.m.lookup L.length = some e := by rw [habove _ hx (Nat.le_refl _)]; exact he
  have := hhi1 _ _ hs
  omega

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- (hraft_robust R5) **What the restore needs of the latest snapshot** (persistent; `latestOk` and
`latestDur`'s facts, read by `NewRaft` from the crash state): its bytes a snapshot of its index (`snapP`), the
committed entry of its term there, durable at `i` or installed while `i` followed, its configuration the
committed one at its index (`snapCfg`), version 1 and no `Peers`. -/
def latFacts (γ : GNames) (rc : RCtx GF) (i : SID) (lat : SnapLatest) : IProp GF :=
  match lat with
  | none => iprop(True)
  | some (m, b) => iprop(□ rc.snapP (uint.nat m.Index') b ∗
      (∃ e : Entry, CIdx γ (uint.nat m.Index') e ∗ ⌜e.term = uint.nat m.Term' ∧ 1 ≤ uint.nat m.Index'⌝) ∗
      (durLb γ i (uint.nat m.Index') ∨ snapFollow γ i (uint.nat m.Index') (uint.nat m.Term')) ∗
      (∃ ss : List Server, cfgVal γ m.Configuration' ss ∗
        snapCfg γ (uint.nat m.Index') (uint.nat m.ConfigurationIndex') ss) ∗
      ⌜m.Version' = W64 1 ∧ m.Peers' = slice.nil⌝)

instance latFacts_persistent γ rc i lat : Persistent (latFacts (GF := GF) γ rc i lat) := by
  unfold latFacts; rcases lat with _ | ⟨_, _⟩ <;> infer_instance

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
    · intro d h; cases h
    · intro _ k e h hk
      have : k = 0 := by omega
      subst this; rw [genesisStore_lookup] at h; simp at h
  · simp only [initSrv, hm, ite_false]
    refine ⟨trivial, trivial, trivial, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_⟩
    · intro k e h; simp [LogAbs.store, LogAbs.empty, LogAbs.ins] at h
    · left; rfl
    · intro k _ hk; simp at hk; omega
    · intro d h; cases h
    · intro _ k e h; simp [LogAbs.store, LogAbs.empty, LogAbs.ins] at h

end fresh

end github_com.hashicorp.raft

end Perennial

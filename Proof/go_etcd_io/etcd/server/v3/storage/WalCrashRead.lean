/- Lean-first (no Rocq counterpart).

# What a restart reads from a WAL a crash left: the read's facts (etcd-dist D6, task T5)

`notes/etcd-dist-d6.md` §2 (the row "`walReadFacts σ` of a crash image") and §6 (T5);
`notes/wal-p8-handoff.md`. Since the torn-`Save` fix (P6, `notes/etcd-dist-d6.md` §10) a crash leaves a
complete prefix `H.take j` of the WAL's history, at or past the synced mark (`walImgS`). The restart
reads it as `walRead (H.take j)`. This module proves, of any read `walRead I = some σ`, the WAL
interface's facts I1-I4 (`notes/wal-crash-handoff/restart-wal-interface.md` §2), which the server
states as `walReadFacts σ` (`etcdserver/WalApi.lean`; the server-side statement is
`etcdserver/SrvCrash.lean`'s `walReadFacts_of_read`):

* I1, the entries consecutive from the base: `walReadCut_wf`, no premise;
* I2, the last index at most `B`: `walReadCut_last_le`, from `walIdxLe B I` (every index of the history
  at most `B`);
* I3, `σ.b ≤ σ.commit` (`walReadCut_b_le_commit`, no premise) and `σ.commit ≤ σ.last`, from
  `walCommitLe I` (raft's `committed ≤ lastIndex` along the read's fold: `walRead_commit_le_last`);
* I4, the fresh base without a snapshot record or a data-less record at the base: `walRead_snapBase`.

The two history conditions pass to prefixes (`walIdxLe_take`, `walCommitLeFrom_take`), so an
invariant that keeps them of the whole history gives them of every crash image (`walCommitLe_take`:
over the reader's filtered fold it needs the eager fold's base at or below its commit, as
`walCommitLe_of_fold`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalLinkPure

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

section crashRead
variable [GooseExts]

/-- **I4 of a read from the first file**: the fresh base `(0, 0)` without a snapshot record, or a
data-less snapshot record at the base. -/
theorem walRead_snapBase {I : WalHist} {σ : StorContents} (h : walRead I = some σ) :
    (σ.snap = none ∧ σ.base = entryID.mk (W64 0) (W64 0)) ∨
      ∃ m, σ.snap = some (SnapshotM.mk [] m) ∧ σ.base = entryID.mk m.Term' m.Index' := by
  unfold walRead at h
  have := walFoldChkFrom_snapInv
    (fun sn b => (sn = none ∧ b = entryID.mk (W64 0) (W64 0)) ∨
      ∃ m, sn = some (SnapshotM.mk [] m) ∧ b = entryID.mk m.Term' m.Index')
    (fun m => Or.inr ⟨m, rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩) h
  exact this

/-- **I3's second half**: under `walCommitLe I`, a read's commit is at most its last index (the
read is the whole filtered fold, a prefix of itself). -/
theorem walRead_commit_le_last {I : WalHist} {σ : StorContents} (hc : walCommitLe I)
    (h : walRead I = some σ) : σ.commit ≤ σ.last := by
  unfold walCommitLe walCommitLeFrom at hc
  unfold walRead at h
  apply hc (I.filter (walKeep (uint.nat (walLastHS I).Commit'))).length σ
  rw [List.take_length]; exact h

/-- **I2**: a read's last index is at most a bound of the history's indexes. -/
theorem walRead_last_le {B : Nat} {I : WalHist} {σ : StorContents} (hB : walIdxLe B I)
    (h : walRead I = some σ) : σ.last ≤ B :=
  walReadCut_last_le (k := 0) hB (by rw [walReadCut_zero]; exact h)

/-- **I1**: a read's entries are consecutive from its base. -/
theorem walRead_wf {I : WalHist} {σ : StorContents} (h : walRead I = some σ) : walEntsWf σ :=
  walReadCut_wf (k := 0) (by rw [walReadCut_zero]; exact h)

/-- **I3's first half**: a read's base is at or below its commit. -/
theorem walRead_b_le_commit {I : WalHist} {σ : StorContents} (h : walRead I = some σ) :
    σ.b ≤ σ.commit :=
  walReadCut_b_le_commit (k := 0) (by rw [walReadCut_zero]; exact h)

/-! ## The history conditions pass to the crash images (prefixes) -/

/-- `walIdxLe` of a history gives it of every prefix. -/
theorem walIdxLe_take {B : Nat} {I : WalHist} (h : walIdxLe B I) (j : Nat) : walIdxLe B (I.take j) :=
  ⟨fun hs es e ho he => h.1 hs es e (List.mem_of_mem_take ho) he,
    fun m al ho => h.2 m al (List.mem_of_mem_take ho)⟩

/-- `walCommitLeFrom` of a history gives it of every prefix (its prefixes are the history's). -/
theorem walCommitLeFrom_take {τ : StorContents} {L : WalHist} (h : walCommitLeFrom τ L) (j : Nat) :
    walCommitLeFrom τ (L.take j) := by
  intro n τ' hn
  rw [List.take_take] at hn
  exact h (min n j) τ' hn

/-- **`walCommitLe` of a crash image** (a prefix `H.take j`) from the eager fold's condition along the
whole history: the eager fold of the prefix succeeds at a state whose base is at or below its commit
(`walCommitLe_of_fold`). -/
theorem walCommitLe_take {H : WalHist} {j : Nat} {τ : StorContents}
    (hc : walCommitLeFrom walFresh H) (hf : walFoldChkFrom walFresh (H.take j) = some τ)
    (hb : τ.b ≤ τ.commit) : walCommitLe (H.take j) :=
  walCommitLe_of_fold hf hb (walCommitLeFrom_take hc j)

end crashRead

end EtcdGrove
end Perennial

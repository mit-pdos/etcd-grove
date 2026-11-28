/-
keepfix (c), 2026-11-28: the WAL's records after `bootstrap`'s catch-up (fork `catchUpWithBackend`,
keepfix-d-term-bbump @828afc98f), and their tie to raft's boot law (`raftBootFix`): `bootHS`, `bootHSB`,
`bootFix` (trusted: they sit in `bootstrapCrashContract`'s text, `InvCrashImage.lean`) and the pure link
`StorageHolds_bootFix` (proved). `~/coordinator-notes/plans/raft-boot-law-brief.md`, the step-2 review list.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.WalRecsCore
public import Proof.go_etcd_io.raft.v3.NodeApiVocab
public import Spec.go_etcd_io.raft.v3.RaftBootFix

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The catch-up's hard state when the WAL holds the backend's entry** (branch A, Go
`bootstrap.go`'s `catchUpWithBackend`): `T = max(ciTerm, raftTerm)`; the term raised to `T` with no
vote if below it; the commit at `i`. -/
def bootHS (σ : StorContents) (i : Nat) (t rt : w64) : HardStateM :=
  let T := if uint.Z t ≤ uint.Z rt then rt else t
  HardStateM.mk (if uint.Z σ.hs.Term' < uint.Z T then T else σ.hs.Term')
    (if uint.Z σ.hs.Term' < uint.Z T then W64 0 else σ.hs.Vote') (W64 i)

/-- **The catch-up's hard state when a snapshot record replaces the log** (branch B, fork 828afc98f:
`st.Term, st.Vote = max(ciTerm, raftTerm, Term_w+1), 0`): a term in which the member neither voted nor
campaigned with the log the record dropped; the commit at `i`. -/
def bootHSB (σ : StorContents) (i : Nat) (t rt : w64) : HardStateM :=
  let T := if uint.Z t ≤ uint.Z rt then rt else t
  HardStateM.mk (if uint.Z σ.hs.Term' < uint.Z T then T else σ.hs.Term' + W64 1) (W64 0) (W64 i)

/-- **The WAL's records after `bootstrap`'s catch-up to the backend's consistent index `i`** (term
`t`, the raft term saved with it `rt`, the members' configuration `cs`): nothing when `i` is within
the WAL's commit; else, when the WAL holds `(i, t)`, its hard state becomes `bootHS`; else a snapshot
record at `(i, t)` (the configuration `cs`) is saved, then the hard state `bootHSB`. -/
def bootFix (σ : StorContents) (i : Nat) (t rt : w64) (cs : ConfStateM) : StorContents :=
  if i ≤ σ.commit then σ
  else if σ.b < i ∧ i ≤ σ.last ∧ (σ.ents[i - σ.b - 1]?).map (·.Term') = some t then
    { σ with hs := bootHS σ i t rt }
  else
    { walSaveSnap σ (SnapshotMetadataM.mk cs (W64 i) t) with hs := bootHSB σ i t rt }

/-- The catch-up does nothing at or below the WAL's commit. -/
theorem bootFix_id (σ : StorContents) (i : Nat) (t rt : w64) (cs : ConfStateM) :
    i ≤ σ.commit → bootFix σ i t rt cs = σ := by
  intro h; unfold bootFix; rw [if_pos h]

/-- **The link of the catch-up's records to raft's boot law** (pure, proved): a storage holding `S`
behind `i` holds, after the catch-up, raft's boot step's state (`raftBootFix`); the branches agree,
the storage's entries being `S`'s from the storage's base, at or below the stored commit. -/
theorem StorageHolds_bootFix (S : RaftState) (σ : StorContents) (i : Nat) (t rt : w64)
    (cs : ConfStateM) (hi : i < 2 ^ 64) :
    StorageHolds S σ → σ.commit < i →
    StorageHolds (raftBootFix S i t rt) (bootFix σ i t rt cs) := by
  intro H Hci
  have H0 := H
  obtain ⟨Hb1, Hbt, Hents, HT, HV, Hbc, Hwc, Hcc, Hsnap, Hbase⟩ := H0
  unfold StorContents.b StorContents.commit at *
  have Hi64 : uint.Z (W64 (i : Int)) = i := by word
  -- the storage's entry at `i` is `S`'s
  have hA : (σ.ents[i - σ.b - 1]?).map (·.Term') = plogTermAt S.base S.ents (W64 (i : Int)) := by
    unfold plogTermAt
    rw [Hi64, Hents]
    unfold RaftState.entsFrom StorContents.b
    have h1 := uint_nat_eq σ.base.index'
    have h2 := uint_nat_eq S.base.index'
    simp only [show ¬ ((i : Int) < uint.Z S.base.index') by omega,
      show ¬ ((i : Int) = uint.Z S.base.index') by omega, ↓reduceIte]
    rw [List.getElem?_drop]
    congr 2
    omega
  have hcond : (σ.b < i ∧ i ≤ σ.last ∧ (σ.ents[i - σ.b - 1]?).map (·.Term') = some t) ↔
      plogTermAt S.base S.ents (W64 (i : Int)) = some t := by
    rw [← hA]
    constructor
    · exact fun h => h.2.2
    · intro h
      refine ⟨by unfold StorContents.b; omega, ?_, h⟩
      unfold StorContents.last StorContents.b
      cases hx : σ.ents[i - σ.b - 1]? with
      | none => rw [hx] at h; cases h
      | some x =>
        have := (List.getElem?_eq_some_iff.mp hx).1
        unfold StorContents.b at this; omega
  unfold raftBootFix bootFix
  simp only [StorContents.commit, show ¬ (i ≤ uint.nat σ.hs.Commit') by omega, ↓reduceIte]
  by_cases HA : plogTermAt S.base S.ents (W64 (i : Int)) = some t
  · rw [if_pos HA, if_pos (hcond.mpr HA)]
    unfold StorageHolds bootHS
    refine ⟨Hb1, Hbt, Hents, ?_, ?_, ?_, ?_, ?_, ?_, Hbase⟩
    · simp only [HT]
    · simp only [HT, HV]
    · simp only [StorContents.b, StorContents.commit]; word
    · simp only [StorContents.commit]; word
    · simp only [StorContents.commit]; word
    · intro sv hsv
      have := Hsnap sv hsv
      simp only [StorContents.b, StorContents.commit] at this ⊢; word
  · rw [if_neg HA, if_neg (fun h => HA (hcond.mp h))]
    unfold StorageHolds bootHSB walSaveSnap
    have hlt : ¬ (uint.nat (W64 (i : Int)) < uint.nat σ.base.index') := by
      have := uint_nat_eq σ.base.index'; word
    have hle : ¬ (uint.nat (W64 (i : Int)) ≤ uint.nat σ.hs.Commit') := by
      have := uint_nat_eq σ.hs.Commit'; word
    simp only [hlt, hle, ↓reduceIte, StorContents.commit, StorContents.b]
    have hbase : plogTermAt (entryID.mk t (W64 (i : Int))) [] (W64 (i : Int)) = some t := by
      unfold plogTermAt; simp
    refine ⟨Int.le_refl _, hbase, by simp [RaftState.entsFrom], by simp [HT], trivial, Nat.le_refl _,
      Nat.le_refl _, Nat.le_refl _, ?_, fun h => absurd rfl h⟩
    intro sv hsv
    cases hsv
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩

end pure

end EtcdGrove
end Perennial

/-
Lean-first (no Rocq counterpart).

# `opOwnSnap`'s oracle: the candidates' unlock bounds raised before `ReleaseLockTo` (W4c U5, tenth session)

`opOwnSnap` (wal.go), after `saveSnap(a, terms[a])`, raises every candidate's unlock bound to the name
bound of its history at `a` (`nameBound(h, a)`, Go's `>` on `uint64`), stores the oracle, then calls
`ReleaseLockTo(a)`, which raises the WAL state's `unl` to `walReleasePos H a`. Here:

* `tRaiseCand o a cd`, `tRaiseNames o a`: the raise, a pure model of the candidates loop;
* the raised oracle's encoding has the same length (only `unl` values change), the same histories and
  marks, and keeps `tMemOk`, `tMemHs`, `tCheckWf`, `tMemSim` with the raised candidate;
* `tReleaseD d a`: `ReleaseLockTo`'s update; the raised candidate still accounts for it (`tMemOk`,
  `walReleasePos ≤ walOpenPos ≤ walNameBound … false = tNameBound`).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.MemberSim
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RefLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open go_etcd_io.raft.v3 WalEnc

section pure
variable [GooseExts]

/-- A candidate with its unlock bound raised to its history's name bound at `a`. -/
def tRaiseCand (o : TOracle) (a : w64) (cd : TCand) : TCand :=
  { cd with unl := if uint.nat cd.unl < uint.nat (tNameBound (tCandHist o cd) a) then
      tNameBound (tCandHist o cd) a else cd.unl }

/-- **The oracle with every candidate's unlock bound raised** (`opOwnSnap`'s loop). -/
def tRaiseNames (o : TOracle) (a : w64) : TOracle :=
  { o with cands := o.cands.map (tRaiseCand o a) }

theorem tRaiseCand_h (o : TOracle) (a : w64) (cd : TCand) : (tRaiseCand o a cd).h = cd.h := rfl

theorem tRaiseNames_hist (o : TOracle) (a : w64) (cd : TCand) :
    tCandHist (tRaiseNames o a) (tRaiseCand o a cd) = tCandHist o cd := rfl

theorem tRaiseNames_mark (o : TOracle) (a : w64) (cd : TCand) :
    tCandMark (tRaiseNames o a) (tRaiseCand o a cd) = tCandMark o cd := rfl

theorem tRaiseCand_unl (o : TOracle) (a : w64) (cd : TCand) :
    uint.nat cd.unl ≤ uint.nat (tRaiseCand o a cd).unl ∧
      uint.nat (tNameBound (tCandHist o cd) a) ≤ uint.nat (tRaiseCand o a cd).unl := by
  unfold tRaiseCand; simp only; split <;> omega

theorem tRaiseNames_length (o : TOracle) (a : w64) :
    (tEncodeOracle (tRaiseNames o a)).length = (tEncodeOracle o).length := by
  rw [tEncodeOracle_length, tEncodeOracle_length]
  simp [tOrRest, tRaiseNames, List.length_flatMap, tRaiseCand, tU64_length, Function.comp_def]

theorem tRaiseNames_mem {o : TOracle} (a : w64) {cd : TCand} (h : cd ∈ o.cands) :
    tRaiseCand o a cd ∈ (tRaiseNames o a).cands := List.mem_map_of_mem h

theorem tMemOk_raise {o : TOracle} {c : TCand} {d : WalDur} (h : tMemOk o c d) (a : w64) :
    tMemOk (tRaiseNames o a) (tRaiseCand o a c) d := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨h1, tRaiseNames_mem a h2, h3, h4, h5, h6, Nat.le_trans h7 (tRaiseCand_unl o a c).1, h8, h9,
    h10, h11⟩

theorem tMemHs_raise {o : TOracle} {d : WalDur} (h : tMemHs o d) (a : w64) : tMemHs (tRaiseNames o a) d := h

theorem tCheckWf_raise {o : TOracle} (h : tCheckWf o) (a : w64) : tCheckWf (tRaiseNames o a) := by
  refine ⟨h.1, ?_⟩
  intro cd hcd
  obtain ⟨cd0, hcd0, rfl⟩ := List.mem_map.1 hcd
  exact h.2 cd0 hcd0

theorem tMemSim_raise {o : TOracle} {c : TCand} {bs l cm : w64} (h : tMemSim o c bs l cm) (a : w64) :
    tMemSim (tRaiseNames o a) (tRaiseCand o a c) bs l cm := h

theorem tOrRoom_raise {o : TOracle} {n : Nat} (h : tOrRoom o n) (a : w64) : tOrRoom (tRaiseNames o a) n := by
  unfold tOrRoom at *; rw [tRaiseNames_length]; exact h

/-- `ReleaseLockTo(a)`'s update. -/
def tReleaseD (d : WalDur) (a : w64) : WalDur :=
  { d with unl := max d.unl (walReleasePos (d.H.map WalOpG.toM) a) }

/-- **The raised candidate accounts for `ReleaseLockTo`'s update.** -/
theorem tMemOk_release {o : TOracle} {c : TCand} {d : WalDur} (h : tMemOk o c d) (a : w64)
    (hl : (tCandHist o c).length < 2 ^ 64) :
    tMemOk (tRaiseNames o a) (tRaiseCand o a c) (tReleaseD d a) := by
  have hr := tMemOk_raise h a
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hr
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, h8, h9, h10, h11⟩
  show max d.unl (walReleasePos (d.H.map WalOpG.toM) a) ≤ uint.nat (tRaiseCand o a c).unl
  apply Nat.max_le.2
  refine ⟨h7, ?_⟩
  have hH : d.H.map WalOpG.toM = (tCandHist o c).map absOp := h4
  rw [hH]
  have e1 := walReleasePos_le_openPos ((tCandHist o c).map absOp) a
  have e2 : walOpenPos ((tCandHist o c).map absOp) a ≤
      walNameBound ((tCandHist o c).map absOp) (uint.nat a) false := Nat.min_le_right _ _
  have h9' : tHistWf (tCandHist o c) := h9
  rw [← tNameBound_eq h9' hl a] at e2
  exact Nat.le_trans e1 (Nat.le_trans e2 (tRaiseCand_unl o a c).2)

theorem tReleaseD_H (d : WalDur) (a : w64) : (tReleaseD d a).H = d.H := rfl

end pure

end etcd_wal
end EtcdGrove
end Perennial

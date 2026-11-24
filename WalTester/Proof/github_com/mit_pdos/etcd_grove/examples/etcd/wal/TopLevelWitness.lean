/- Lean-first (no Rocq counterpart).

# The WAL tester: its top-level statement's premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): `etcd_wal_safe`'s premises hold together with
`Robust`'s antecedents (under the tester's semantics, whose `initLocal` is Perennial's default). The
machine's file system has two roots, the area `/w` (inode 0) and the oracle directory `/o` (inode 1),
both empty, and nothing else (`fsRoots`, `Robustness/FsStart.lean`): so the first boot's facts
(`tFirst`) hold, and the paths (`/o/state`, `/w/wal`, `/w/wal.tmp`) are clean and fit, by evaluation.
(`Hopen`, an Iris contract, is left out by `premise_sat%` itself.) Checked by
`etc/premise-witness.py`.
-/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.TopLevelRobustness
public import Robustness.FsStart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3 Fs WalEnc WalFs

attribute [local instance] fsExts fsExtsInterp tExtsSem tFsSem tFsSemOk tHasFs tSat tSatL

open Robustness

/-- The witness's roots: the area and the oracle directory. -/
abbrev tRoots : List GoString := [go!"/w", go!"/o"]

theorem tRoots_init : FsInit (fsRoots tRoots) :=
  fsInit_fsRoots _ (by decide)
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact rootForm_one _ (by decide))
    (by decide)

/-- The witness's environment. -/
def tEnv0 : TEnv := ⟨go!"/w", go!"/o", (fsRoots tRoots).fs.roots, 0, 1⟩

theorem tEnv0_orFile_ok : tEnv0.orFile.Ok := by
  refine ⟨⟨[go!"o"], by simp, ?_, by decide⟩, ?_, ?_, by decide, by decide, by decide⟩
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    unfold EtcdGrove.path.cleanSeg; decide
  · unfold EtcdGrove.path.cleanSeg; decide
  · unfold EtcdGrove.path.cleanSeg; decide

theorem tEnv0_paths : tWalPathsOk tEnv0.area := by
  refine ⟨⟨by unfold walNameOk; decide, by decide⟩, by decide, ⟨[go!"w"], by simp, ?_, by decide⟩,
    by decide⟩
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  unfold pathElemOk; decide

theorem etcd_wal_safe.premisesSat : premise_sat% etcd_wal_safe.spec := by
  intros
  exact ⟨freshState (fsRoots tRoots, ()), ⟨((), ()), ∅⟩, tEnv0,
    tRoots_init, rfl, by decide, by decide, by decide, tEnv0_orFile_ok, tEnv0_paths,
    ⟨⟨by decide, winOk_short (by decide)⟩, ⟨by decide, winOk_short (by decide)⟩⟩,
    ⟨rfl, (fsRoots_mem _ 0).2 (by decide), fun _ _ => fsRoots_entry _ _ _,
      (fsRoots_mem _ 1).2 (by decide), fsRoots_entry _ _ _, fsRoots_entry _ _ _⟩,
    (robustStart_one (σ := freshState (fsRoots tRoots, ())) (g := ⟨((), ()), ∅⟩)
      (fresh_freshState _) (by exts_init) (by exts_init)).2⟩

end etcd_wal
end EtcdGrove
end Perennial

end

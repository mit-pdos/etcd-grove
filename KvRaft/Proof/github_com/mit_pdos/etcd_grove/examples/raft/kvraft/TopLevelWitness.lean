/- Lean-first (no Rocq counterpart).

# `raft/kvraft`: its top-level statements' premises are satisfiable

`premise_sat%` (`Robustness/PremiseSat.lean`): `kvraft_robust`'s and `kvraft_robust_example`'s premises
hold together with `Robust`'s antecedents. Every machine (the replicas' and the client's) starts as
`kvStart`: a fresh process with no listener (`Net.NetLocal.init`) whose file system is the root
`/var/lib/kvraft` alone, empty (`Robustness/FsStart.lean`: `FsInit`, and nothing below `dir`); the
network has no connection (`Net.NetGlobal.init`). `kvraft_robust`'s witness is one replica at
`10.0.0.1:7001` with the example's options; the example's, its five replicas. Nothing is left out.
Checked by `etc/premise-witness.py`.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.TopLevelRobustness
public import Robustness.FsStart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open NetFs Robustness Fs

/-- The witnesses' directory, a root of every machine's file system. -/
def witnessDir : GoString := go!"/var/lib/kvraft"

theorem witnessDir_rootForm : RootForm witnessDir :=
  ⟨[go!"var", go!"lib", go!"kvraft"], by simp, by decide, by decide⟩

section witness
attribute [local instance] kvraftExts kvraftExtsSemantics kvraftExts_hasNet kvraftExts_hasFs
variable [go_gctx : GoGlobalContext]

/-- Every machine's start: a fresh process, no listener, the empty root `witnessDir`. -/
def kvStart [lctx : GoLocalContext] : state :=
  freshState ((default : Net.NetLocal), fsOneRoot witnessDir, ())

/-- The network's start: no connection. -/
def kvStartG : GlobalState := ⟨((default : Net.NetGlobal), (), ()), ∅⟩

theorem kvStart_fs [lctx : GoLocalContext] : fsOf kvStart = fsOneRoot witnessDir := rfl

/-- The premise on a machine: `witnessDir` an empty root of its file system. -/
theorem kvStart_dir [lctx : GoLocalContext] :
    witnessDir ∈ (fsOf kvStart).fs.roots.map (·.1) ∧
      ∀ c, (fsOf kvStart).lookup (joinPath witnessDir [c]) = none := by
  rw [kvStart_fs]
  exact ⟨by simp [fsOneRoot], fun c => fsOneRoot_lookup_child _ c⟩

theorem kvStart_initLocal [lctx : GoLocalContext] : extsInitLocal kvStart kvStartG := by
  exact ⟨rfl, fsInit_fsOneRoot _ witnessDir_rootForm, trivial⟩

theorem kvStart_initGlobal : extsInitGlobal kvStartG := by
  exts_init

theorem kvraft_robust.premisesSat : premise_sat% kvraft_robust.spec := by
  intros
  refine ⟨exampleConfig, witnessDir, [(go!"10.0.0.1:7001", kvStart)], kvStart, kvStartG, ?_, ?_⟩
  · intro a σ h
    obtain ⟨-, rfl⟩ : a = go!"10.0.0.1:7001" ∧ σ = kvStart := by simpa using h
    exact kvStart_dir
  · exact robustStart_same (σ := kvStart) (by simp) (fresh_freshState _) kvStart_initGlobal
      kvStart_initLocal

theorem kvraft_robust_example.premisesSat : premise_sat% kvraft_robust_example.spec := by
  intros
  refine ⟨kvStart, kvStart, kvStart, kvStart, kvStart, kvStart, kvStartG, ?_, ?_⟩
  · intro σ h
    obtain rfl : σ = kvStart := by simpa using h
    exact kvStart_dir
  · exact robustStart_same (σ := kvStart) (by simp) (fresh_freshState _) kvStart_initGlobal
      kvStart_initLocal

end witness

end kvraft
end EtcdGrove
end Perennial

end

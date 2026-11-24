/- Lean-first (no Rocq counterpart).

# `osfs/crashlog`: the top-level robustness result, stated

`crash_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/osfs/crashlog/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.crashlog.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace osfs_crashlog

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.crashlog

open Fs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- **`crash_safety` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that may crash at any step and restart,
a fresh Go process (`Robust`'s premise), under `crash_safety`'s other hypotheses: in every
execution of fewer than `bound` steps no thread is stuck and none has an unrecovered panic. -/
def crash_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (σ : state) (g : GlobalState) (dir : GoString) (Hinit : FsInit (extLocal fsExt σ.world))
    (Hdir : ∃ j, (dir, j) ∈ (extLocal fsExt σ.world).fs.roots)
    (Hnd : ∀ J, (extLocal fsExt σ.world).lookup (child dir logB) ≠ some (.dir J))
    (Hlog : ∀ k, (extLocal fsExt σ.world).lookup (child dir logB) = some (.file k) →
      Good ((extLocal fsExt σ.world).fs.files !! k))
    (bound : Nat),
    Robustness.Robust [(boot dir, σ)] [] g (threads := bound + 1) (bound := bound)

end adequacy
end osfs_crashlog
end EtcdGrove
end Perennial

end

/- Lean-first (no Rocq counterpart).

# `osfs/walfs`: the top-level robustness results, stated

`dirswap_crash_robust`, `crash_robust`, `seglog_crash_robust`: the example's closed theorems as instances of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states them (to audit); the proofs are in
`Proof/github_com/mit_pdos/etcd_grove/examples/osfs/walfs/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.DirSwapResults
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.SegLogResults
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.walfs.TopLevelDefs

@[expose] public section

noncomputable section

section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

open Fs DSBase DS
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- **`dirswap_crash_safety` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that may crash at any step and restart,
a fresh Go process (`Robust`'s premise), under `dirswap_crash_safety`'s other hypotheses: in every
execution of fewer than `bound` steps no thread is stuck and none has an unrecovered panic. -/
def dirswap_crash_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.file.FieldAssumptions]
    (σ : state) (g : GlobalState) (dir : GoString) (j : Ino)
    (Hinit : FsInit (extLocal fsExt σ.world)) (Hdir : (dir, j) ∈ (extLocal fsExt σ.world).fs.roots)
    (Hsafe : DS.SafeT j none (extLocal fsExt σ.world).fs.treeDur ∨
      ∃ k, DS.SafeT j (some k) (extLocal fsExt σ.world).fs.treeDur ∧
        ∃ f, (extLocal fsExt σ.world).fs.files !! k = some f ∧ DS.DataGood (some f))
    (bound : Nat),
    Robustness.Robust [(bootDS dir, σ)] [] g (threads := bound + 1) (bound := bound)

end adequacy
end osfs_walfs
end EtcdGrove
end Perennial

end

section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

open Fs
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- **`crash_safety` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that may crash at any step and restart,
a fresh Go process (`Robust`'s premise), under `crash_safety`'s other hypotheses: in every
execution of fewer than `bound` steps no thread is stuck and none has an unrecovered panic. -/
def crash_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.file.FieldAssumptions]
    (σ : state) (g : GlobalState) (dir : GoString) (Hinit : FsInit (extLocal fsExt σ.world))
    (Hdir : ∃ j, (dir, j) ∈ (extLocal fsExt σ.world).fs.roots)
    (Hnd : (∀ J, (extLocal fsExt σ.world).lookup (child dir segB) ≠ some (.dir J)) ∧
      (∀ J, (extLocal fsExt σ.world).lookup (child dir tmpB) ≠ some (.dir J)))
    (Hseg : ∀ k, (extLocal fsExt σ.world).lookup (child dir segB) = some (.file k) →
      DataGood ((extLocal fsExt σ.world).fs.files !! k))
    (bound : Nat),
    Robustness.Robust [(boot dir, σ)] [] g (threads := bound + 1) (bound := bound)

end adequacy
end osfs_walfs
end EtcdGrove
end Perennial

end

section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace osfs_walfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

open Fs DSBase
  github_com.mit_pdos.etcd_grove.examples.osfs.walfs

attribute [local instance] fsExts fsExtsSemantics fsExtsInterp fsExts_hasFs fsExtsCrashInterp

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- **`seglog_crash_safety` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that may crash at any step and restart,
a fresh Go process (`Robust`'s premise), under `seglog_crash_safety`'s other hypotheses: in every
execution of fewer than `bound` steps no thread is stuck and none has an unrecovered panic. -/
def seglog_crash_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.file.FieldAssumptions]
    (σ : state) (g : GlobalState) (dir : GoString) (Hinit : FsInit (extLocal fsExt σ.world))
    (Hdir : ∃ j, (dir, j) ∈ (extLocal fsExt σ.world).fs.roots) (bound : Nat),
    Robustness.Robust [(bootLog dir, σ)] [] g (threads := bound + 1) (bound := bound)

end adequacy
end osfs_walfs
end EtcdGrove
end Perennial

end

end

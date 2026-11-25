/- Lean-first (no Rocq counterpart).

# `osfs/bboltfs`: the top-level robustness result, stated

`bootCrashRobust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/osfs/bboltfs/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.TopLevelDefs

@[expose] public section

noncomputable section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace EtcdGrove

namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

open Fs

attribute [local instance] fsExts fsExtsInterp

local instance : GooseSemantics := fsExtsSemanticsWithS AnyStep P1

local instance : ExtSemantics fsExt := fsSemWithS AnyStep P1

local instance : HasExt fsExt := fsExtsWithS_hasFs AnyStep P1

section adequacy

variable [GoGlobalContext] {GF : BundledGFunctors}

/-- **`bootCrashSafety` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`), under P1's semantics: the program alone on one machine that may
crash at any step and restart, a fresh Go process (`Robust`'s premise), its files as on disk, its
directory a root with no `db` in it: in every execution of fewer than `2 ^ 63` steps along which
fewer than `2 ^ 30` threads are live at once (`Robust`'s thread bound, the one minibolt's proof
needs), no thread is stuck and none has an unrecovered panic. (Until 2026-11-24 the step bound was
`2 ^ 30 - 1`: the crash adequacy theorem took the thread bound of every execution, which only the
step count bounded; Perennial's `goose_crash_adequacy_below` takes it along the execution.) -/
def bootCrashRobust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics] [package_sem : Assumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] (dir : GoString)
    (σ : state) (g : GlobalState)
    (Hinit : FsInit (extLocal fsExt σ.world))
    (Hdir : ∃ j, (dir, j) ∈ (extLocal fsExt σ.world).fs.roots)
    (Hnone : (extLocal fsExt σ.world).lookup (dir ++ go!"/db") = none),
    Robustness.Robust [(boot dir, σ)] [] g (threads := 2 ^ 30)
      (bound := 2 ^ 63)

end adequacy
end osfs_bboltfs
end EtcdGrove
end Perennial

end

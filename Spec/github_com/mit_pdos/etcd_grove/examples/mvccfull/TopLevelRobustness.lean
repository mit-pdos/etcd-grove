/- Lean-first (no Rocq counterpart).

# `mvccfull`: the top-level robustness result, stated

`mvccfull_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/mvccfull/TopLevelRobustness.lean`.
-/
module

public import GooseLang.Ext.Fs.PathFitsLemmas
public import Code.go_etcd_io.etcd.server.v3.etcdserver
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.TopLevelDefs
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI

section adequacy

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr

variable [go_gctx : GoGlobalContext]

/-- **`mvccfull_safe` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `mvccfull_safe`'s other hypotheses: in every
execution of fewer than `2 ^ 48` steps along which fewer than `2 ^ 28` threads are live, no thread
is stuck and none has an unrecovered panic. -/
def mvccfull_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
    [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions] [os.file.FieldAssumptions]
    [os.fileStat.FieldAssumptions] (r : GoString)
    (HEnv : verifyEnvOff (mvccfullProgram r))
    (σ : state) (g : GlobalState) (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)) (j0 : Fs.Ino)
    (Hr : (r, j0) ∈ (extLocal Fs.fsExt σ.world).fs.roots)
    (Habs : ∀ b ∈ mvccfull.mvccfullNames, (extLocal Fs.fsExt σ.world).fs.treeDur.entry j0 b = none)
    (Hrfit : Fs.DirFits r),
    Robustness.Robust [] [(mvccfullProgram r, σ)] g (threads := 2 ^ 28)
      (bound := 2 ^ 48)

end adequacy
end EtcdGrove
end Perennial

end

/- Lean-first (no Rocq counterpart).

# `mvccrand`: the top-level robustness result, stated

`mvccrand_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g threads bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps along which every machine keeps fewer than `threads` threads,
no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/mvccrand/TopLevelRobustness.lean`.
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TopLevelDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.TopLevelDefs
public import Spec.sort.Slice
public import GooseLang.Ext.Fs.PathFitsLemmas

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr

section adequacy

variable [go_gctx : GoGlobalContext]

/-- **`mvccrand_adequate` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `mvccrand_adequate`'s other hypotheses: in every
execution of fewer than `2 ^ 38` steps along which fewer than `2 ^ 28` threads are live, no thread
is stuck and none has an unrecovered panic. -/
def mvccrand_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
    [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    (Hsort : ∀ hG : HeapGS .hasLC mvccrandGF,
      sort.Slice.spec (GF := mvccrandGF) (hG := heapWith hG lctx))
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] (r : GoString)
    (HEnv : verifyEnvOff (mvccrandProgram r)) (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world)) (j0 : Fs.Ino)
    (Hr : (r, j0) ∈ (extLocal Fs.fsExt σ.world).fs.roots)
    (Habs : (extLocal Fs.fsExt σ.world).fs.treeDur.entry j0 go!"mvccrand.db" = none)
    (Hrfit : Fs.DirFits r),
    Robustness.Robust [] [(mvccrandProgram r, σ)] g (threads := 2 ^ 28)
      (bound := 2 ^ 38)

end adequacy
end EtcdGrove
end Perennial

end

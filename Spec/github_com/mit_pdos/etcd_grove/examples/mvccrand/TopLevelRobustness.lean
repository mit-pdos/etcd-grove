/- Lean-first (no Rocq counterpart).

# `mvccrand`: the top-level robustness result, stated

`mvccrand_robust`: the example's closed theorem as an instance of the generic robustness statement
(`Robustness/Statement.lean`, `Robust crashing stable g bound`: in every execution of the
machines that may crash and restart and of those that never crash, each a fresh Go process, of
fewer than `bound` steps, no thread is stuck and none has an unrecovered panic). This file only
states it (to audit); the proof is in
`Proof/github_com/mit_pdos/etcd_grove/examples/mvccrand/TopLevelRobustness.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Adequacy
public import Robustness.Statement

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

section adequacy

variable [go_gctx : GoGlobalContext]

/-- **`mvccrand_adequate` as a robustness statement** (`Robustness.Robust`,
`Robustness/Statement.lean`): the program alone on one machine that never crashes,
a fresh Go process (`Robust`'s premise), under `mvccrand_adequate`'s other hypotheses: in every
execution of fewer than `2 ^ 28 - 1` steps no thread is stuck and none has an unrecovered panic. -/
def mvccrand_robust.spec : Prop :=
  ∀ [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
    [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    (Hsort : ∀ hG : HeapGS .hasLC mvccrandGF,
      sort.Slice.spec (GF := mvccrandGF) (hG := heapWith hG lctx))
    (Hdbo : backend.dbOpenOk) (Hdbc : backend.dbCloseOk)
    (HFs : dbFilesAbsent mvccrandProgram [go!"mvccrand.db"]) (HEnv : verifyEnvOff mvccrandProgram)
    (σ : state) (g : GlobalState),
    Robustness.Robust [] [(mvccrandProgram, σ)] g (2 ^ 28 - 1)

end adequacy
end EtcdGrove
end Perennial

end

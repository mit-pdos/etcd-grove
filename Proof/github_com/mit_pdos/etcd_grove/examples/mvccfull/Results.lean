/-
mvcc's full tester's results (`examples/mvccfull/mvccfull.go`, `notes/mvccfull.md`), restated, with
the trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`mvccfull_Main`** (`Link.lean`'s `mvccfull.wp_Main`): `Main()` -- `Run(MainConfig("mvccfull"))`:
  two members over real backends and lessors, the writer's log (puts, deletes, transactions, lease
  grants and revokes, compactions, snapshot installs, clean restarts), readers and watch streams on
  both members, every result checked against the tester's model (a check that fails panics), each
  member closed, reopened, read in full and closed -- returns; so every check passes. From the
  package's `isPkgInit`, `Main`'s files absent, the thread and receipt bounds,
  `ckptEffectsOk`, `dbOpenOk` and `dbCloseOk`
  (`Spec/github_com/mit_pdos/etcd_grove/examples/mvccfull/Main.lean`; until premise fixes 5,
  2026-11-10, also `keySized`, now proved: `mvcc.keySized_all`).
* **`mvccfull_safe`** (`Adequacy.lean`'s `mvccfull_adequate`): the closed theorem. Every real
  execution of `n` steps of `mvccfull`'s initialization followed by `Main()`, from a fresh state
  with one thread: the main thread's result, if any, is `#()`, no thread is stuck, none has
  panicked; under mvccrand's hypotheses but `sort.Slice.spec` (see `Adequacy.lean`'s header).
  Executions of fewer than `2 ^ 28` steps only (`n + 2 ≤ 2 ^ 28`), and a full-size run of `Main`
  is longer: the theorem covers each prefix of a run of that length, not a complete run (mvcc-r3-1).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Adequacy

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Every check of mvcc's full tester passes** (`Link.lean`'s `mvccfull.wp_Main`; see the file
header). -/
theorem mvccfull_Main [go_etcd_io.etcd.cache.v3.Assumptions] :
    mvccfull.Main.spec (GF := GF) (hG := hG) :=
  mvccfull.wp_Main

end results

section adequacy
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt
variable [go_gctx : GoGlobalContext]

/-- **mvcc's full tester passes, in the operational semantics** (`mvccfull_adequate`, see the file
header and `Adequacy.lean`). -/
theorem mvccfull_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
    [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    (Hck : ckptEffectsOk) (Hdbo : backend.dbOpenOk) (Hdbc : backend.dbCloseOk)
    (HFs : dbFilesAbsent mvccfullProgram
      (mvccfull.filePathsM (mvccfull.mainConfigM go!"mvccfull"
        (zeroValDef : github_com.mit_pdos.etcd_grove.examples.mvccfull.Mix))))
    (HEnv : verifyEnvOff mvccfullProgram)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([mvccfullProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  mvccfull_adequate Hck Hdbo Hdbc HFs HEnv σ g Hlctx Hinit Hthreads n κs t2 σ2 Hsteps Hn

end adequacy

#print axioms mvccfull_Main
#print axioms mvccfull_adequate
#print axioms mvccfull_safe

end EtcdGrove
end Perennial

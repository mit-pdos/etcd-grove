/- Lean-first (no Rocq counterpart).

# mvcc's randomized tester's closed theorem (2026-11-08)

A closed theorem about the operational semantics of `mvccrand`'s program (`examples/mvccrand`): the
package's initialization (which initializes its import closure: mvcc, the lessor, the backend,
zap, ...) followed by `Main()` -- a backend in the fresh file `mvccrand.db`, the lessor and the
store over it as etcd's server makes them, the writer's 1000 random operations, 4 readers and a
watch stream's registrar and receiver running concurrently, every result of mvcc checked against
the tester's model (a failed check panics), then the store, the lessor and the backend closed --
started from a fresh state (no package initialized, one thread): for every real execution of `n`
steps, the main thread's result, if it has one, is `#()`, no thread is stuck, and no thread has
ended in a panic. So no check of the tester fails, in any interleaving.

It follows from `goose_adequacy_start_files` (`Proof/runtime/Start.lean`: Perennial's
`goose_adequacy` whose WP proof also receives program start's rights, here `ETCD_VERIFY` off and the
fresh database file `mvccrand.db`, `fileHolds "mvccrand.db" ∅`), instantiated with the trivial
extension (`etcdstart/TrivialExt.lean`; the proofs are generic over the extensions) and a
ghost-state bundle `mvccrandGF`, from `mvccrand`'s `wp_initialize'` (`Init.lean`, over the
program's package table `PkgTable.lean`) and `mvccrand.wp_Main` (`Link.lean`; `Results.lean`'s
`mvccrand_Main`).

**Its hypotheses**:
* pure facts of the program's environment: `dbOpenOk` and `dbCloseOk` (bbolt's `Open` and `Close`
  do not fail for the environment's reasons: the user's decision, 2026-11-08, "an assumption that
  the backend opening doesn't panic"), `dbFilesAbsent` (`mvccrand.db` absent at start and touched
  only by the backend) and `verifyEnvOff` (`ETCD_VERIFY` unset), and the execution's length
  (`n + 2 ≤ 2 ^ 28`: the thread bound, and with `N = n + 1` the receipt bound `2 ^ 38`);
* a pure fact of the lessor's configuration: `ckptEffectsOk` (`lease.NewLessor`'s);
* the semantics: `go.Semantics` and the package assumptions (`mvccrand`'s, mvcc's, the server's,
  the cache's);
* at every ghost-state instance: `sort.Slice`'s spec (`Spec/sort/Slice.lean`: specified, neither
  proved nor assumed; the writer's lease checks sort with it). (Premise fixes 5, 2026-11-10) Until
  then also the store's key-count premise `keySized` (the backend's read states hold fewer than
  `2 ^ 62` keys), now proved (`mvcc.keySized_all`, from bbolt's address-space bound
  `backend.rtxSnap_size`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Results
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.PkgTable
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TrivialExt
public import Proof.runtime.Start
public import Proof.runtime.Threads

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

/-! ## The ghost-state bundle -/

/-- The functors (as `putgetGF`): the universal camera (`AllG`) at slot 0, then invariants, later
credits, GooseLang's heap, prophecies and package state. Every other slot is the unit functor. -/
def mvccrandGF : BundledGFunctors := fun i =>
  match i with
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)),
          inferInstance⟩
  | 7 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- The universal camera at slot 0. -/
def mvccrandGF_allG : AllG mvccrandGF := ⟨⟨0, rfl⟩⟩

instance mvccrandGF_gooseGpreS : GooseGpreS mvccrandGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨mvccrandGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := mvccrandGF_allG

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- The program: `mvccrand`'s initialization, then `Main()`. -/
def mvccrandProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.mvccrand.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.mvccrand.Main) #()

/-- **mvcc's randomized tester passes** (see the file header): every real execution of
`mvccrandProgram` from a fresh state with one thread, of `n` steps: if the main thread has
finished, its result is `#()` (`Main` returned: every check of mvcc passed); no thread is stuck;
no thread has ended in a panic. -/
theorem mvccrand_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
    [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    (Hsort : ∀ hG : HeapGS .hasLC mvccrandGF,
      sort.Slice.spec (GF := mvccrandGF) (hG := heapWith hG lctx))
    (Hck : ckptEffectsOk) (Hdbo : backend.dbOpenOk) (Hdbc : backend.dbCloseOk)
    (HFs : dbFilesAbsent mvccrandProgram [go!"mvccrand.db"])
    (HEnv : verifyEnvOff mvccrandProgram)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([mvccrandProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  apply adequate_of_unrecovered
  refine goose_adequacy_start_files (GF := mvccrandGF) (n + 1) (n + 2) mvccrandProgram σ g
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) ⟨trivial, trivial⟩
    ⟨trivial, trivial⟩ [] [] [] [go!"mvccrand.db"] List.nodup_nil List.nodup_nil List.nodup_nil
    (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩)
    (fun _ h => absurd h List.not_mem_nil) (fun _ h => absurd h List.not_mem_nil)
    (fun _ h => absurd h List.not_mem_nil) ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
    HFs HEnv ?_ n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads (realThreadsBelow_of_one Hthreads)
  intro hG HN HT HL
  obtain ⟨G, ⟨fl, lc, nh, gs, th, cr⟩⟩ := hG
  subst Hlctx
  subst HL
  letI : HeapGS .hasLC mvccrandGF := ⟨G, ⟨fl, σ.goState.goLctx, nh, gs, th, cr⟩⟩
  -- the hypotheses at this instance (`heapWith` of it, definitionally)
  have Hsort' : sort.Slice.spec (GF := mvccrandGF) := Hsort _
  unfold IsInit at Hinit
  rw [Hinit]
  haveI : ThreadBoundLe mvccrandGF (2 ^ 28) := ⟨by rw [HT]; omega⟩
  haveI : ReceiptBoundLe mvccrandGF (2 ^ 38) := ⟨by rw [HN]; omega⟩
  iintro - - Hgs Htok Hrights Hfiles
  iunfold startRights at Hrights
  icases Hrights with ⟨-, -, -, -, #Hvoff⟩
  icases BigSepL.bigSepL_cons.1 $$ Hfiles with ⟨Hfile, -⟩
  ihave Hown := (ownInitializing_of_empty
    (github_com.mit_pdos.etcd_grove.examples.mvccrand.getIsPkgInit (GF := mvccrandGF))) $$ Hgs
  imodintro
  unfold mvccrandProgram
  wp_apply (github_com.mit_pdos.etcd_grove.examples.mvccrand.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.mvccrand.getIsPkgInit_wf) $$ Hown as ⟨-, #Hpkg⟩
  wp_apply (mvccrand.wp_Main Hsort' Hck Hdbo Hdbc) $$ [Hfile Htok]
  · iframe Hfile Htok Hvoff
  ipureintro
  rfl

end adequacy

#print axioms mvccrand_adequate

end EtcdGrove
end Perennial

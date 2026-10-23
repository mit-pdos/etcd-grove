/- Lean-first (no Rocq counterpart).

# The adequacy example's closed theorem (item 9, stage 3, 2026-10-18)

A closed theorem about the operational semantics of `putget`'s program (`examples/putget`): the
package's initialization (which initializes its import closure: etcd's server, its gRPC layer,
the client, raft, ...) followed by `Main()` -- one etcd member started in process, a client, a
`Put` of `k` with `v`, a `Get` of `k`, and a panic unless the `Get` returned `v` -- started from a
fresh state (no package initialized, one thread): for every real execution of `n` steps, the main
thread's result, if it has one, is `#()`, no thread is stuck, and no thread has ended in a panic.

It follows from `EtcdGrove.goose_adequacy_start` (`Proof/runtime/Start.lean`: Perennial's
`goose_adequacy` whose WP proof also receives program start's rights, D19d) with the read
package's two metric names and the client address `127.0.0.1:23790`, instantiated with the disk
FFI (the proofs are generic over the FFI) and a ghost-state bundle `putgetGF`, from `putget`'s
`wp_initialize'` (`Init.lean`, over the program's package table `PkgTable.lean`) and
`putget_Main` (`Results.lean`).

**Its hypotheses** (D19a; `notes/decisions.md`, D19r):
* pure facts of the program and its environment: `BootFacts id bootLog` (the member id and the
  bootstrap log Go computes), `ckptEffectsOk`, `authRecordsFit`,
  `apply.backendUnderQuota`, `storage.dbOpensOk` (D22 S-j2), `namesUnclaimed`/`addrsUnclaimed` (D19d),
  and the execution's length (`n + 2 ≤ 2 ^ 31`: the thread bound and, with `N = n + 1`, the
  time-receipt bounds; `n + 7 ≤ backend.wbInit`: the backend's write-back budget `bootstrap`'s
  contract gives);
* the semantics: `go.Semantics`, the package assumptions (`putget`'s, the cache's), and the
  method-set and model classes the proofs take (`v3rpc.ServerMethodSets`, `errors.AsTarget` of
  `rpctypes.EtcdError`, `Float64ToInt64Semantics`, `DialWithBalancerBody`, `ErrorStringLeaf`,
  `RpctypesEtcdErrorMethods`, `context.ErrorStringIsError`, `context.DeadlineExceededIsError`,
  `log.NewModel`), and `ContextReadErrs` (`context.Canceled`'s and `DeadlineExceeded`'s method
  facts from `context`'s package fact: the read package's initializer's premise class, item 8);
* triples of functions the program calls, with fresh resources (`putget.premises`: `bootstrap`'s
  contract, the raft wrapper's names-only contracts, `Stop` of a started node,
  `runsNoRequireLeader`), at every ghost-state instance;
* (until 2026-10-20 also two marked hypotheses, false under the then Perennial pin,
  `EofFromIoInit` and `ClosedchanFromContextInit`: `io.EOF` and `context`'s `closedchan` now come
  from their packages' facts, `v3rpc.eofVar_of_init` and `context.isClosedchanInit_of_init`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.putget.PkgTable
public import Proof.runtime.Start
public import Proof.runtime.Threads
public import Perennial.GooseLang.Ffi.DiskFfi.Adequacy

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] disk_op disk_model disk_semantics disk_interp

/-! ## The ghost-state bundle -/

/-- The functors (as the register's `registerGF`): the universal camera (`AllG`) at slot 0, then
invariants, later credits, GooseLang's heap, prophecies and package state, and the disk FFI's
heap. Every other slot is the unit functor. -/
def putgetGF : BundledGFunctors := fun i =>
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
  | 8 => ⟨constOF (HeapView Int (Agree (DiscreteO Block)) (GMap Int)), inferInstance⟩
  | 9 => ⟨constOF (HeapView Int (Agree (DiscreteO GName)) (GMap Int)), inferInstance⟩
  | 10 => ⟨constOF MetaUR, inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

/-- The universal camera at slot 0. -/
def putgetGF_allG : AllG putgetGF := ⟨⟨0, rfl⟩⟩

instance putgetGF_gooseGpreS : GooseGpreS disk_model putgetGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGFfi := (⟨⟨⟨⟨8, rfl⟩⟩, ⟨⟨9, rfl⟩⟩, ⟨10, rfl⟩⟩⟩ : DiskPreG putgetGF)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := putgetGF_allG

/-- **A ghost-state instance at the local context `lctx`** (the hypotheses below are stated over
every instance of the ghost state whose Go local context is the semantics' own). -/
abbrev heapAt (hG : HeapGS .hasLC putgetGF) (lctx : GoLocalContext) : HeapGS .hasLC putgetGF :=
  ⟨hG.goose_globalGS, ⟨hG.goose_localGS.gooseFfiLocalGS, lctx,
    hG.goose_localGS.goose_na_heapGS, hG.goose_localGS.goose_go_stateGS⟩⟩

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- The program: `putget`'s initialization, then `Main()`. -/
def putgetProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.putget.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.putget.Main) #()

/-- The read package's two metric names, which `putget`'s initialization registers (`readRegPerm`,
D16). -/
def putgetNames : List GoString := [read.slowReadIndexName, read.readIndexFailedName]

/-- **The adequacy example is safe** (see the file header): every real execution of
`putgetProgram` from a fresh state with one thread, of `n` steps: if the main thread has finished,
its result is `#()` (`Main` returned: the `Get` that returned `nil` returned the `Put`'s value); no
thread is stuck; no thread has ended in a panic. -/
theorem putget_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.putget.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [ErrorStringLeaf] [RpctypesEtcdErrorMethods] [context.ErrorStringIsError]
    [context.DeadlineExceededIsError] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF, ContextReadErrs (GF := putgetGF) (hG := heapAt hG lctx))
    (Hms : v3rpc.ServerMethodSets)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (id : w64) (bootLog : List EntryM) (Hbf : putget.BootFacts id bootLog)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hdbo : storage.dbOpensOk)
    (HNs : prometheus.namesUnclaimed putgetProgram putgetNames)
    (HAs : addrsUnclaimed putgetProgram [go!"127.0.0.1:23790"])
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ putget.premises (GF := putgetGF) (hG := heapAt hG lctx) n id bootLog)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : g.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([putgetProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 31) (Hwb : n + 7 ≤ backend.wbInit) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  suffices H : (∀ v t2', t2 = Val v :: t2' → v = #()) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) by
    refine ⟨H.1, H.2.1, fun v hv => ?_⟩
    cases h : v.isPanic
    · rfl
    · obtain ⟨p, rfl⟩ := val.isPanic_eq_true h
      exact absurd (UnrecoveredPanic.panic p) (H.2.2 _ hv)
  refine goose_adequacy_start (GF := putgetGF) (n + 1) (n + 2) putgetProgram σ g
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) trivial trivial
    putgetNames [go!"127.0.0.1:23790"] (by decide) (by decide) HNs HAs ?_
    n κs t2 σ2 Hsteps (Nat.lt_succ_self n) Hthreads (realThreadsBelow_of_one Hthreads)
  intro hG HN HT HL
  have Hprem0 := Hprem hG
  have Hctx0 := Hctx hG
  obtain ⟨G, ⟨fl, lc, nh, gs⟩⟩ := hG
  subst Hlctx
  subst HL
  letI : HeapGS .hasLC putgetGF := ⟨G, ⟨fl, σ.goState.goLctx, nh, gs⟩⟩
  haveI := Hctx0
  unfold IsInit at Hinit
  rw [Hinit]
  iintro _ _ Hgs Htok Hrights
  ihave Hown : ownInitializing
      (github_com.mit_pdos.etcd_grove.examples.putget.getIsPkgInit (GF := putgetGF)) $$ [Hgs]
  · rw [ownInitializing_unseal]
    unfold ownInitializingDef
    iexists ∅
    iframe Hgs
    imodintro
    iapply BigSepM.bigSepM_empty.2
    itrivial
  iunfold startRights at Hrights
  simp only [putgetNames, BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
  icases Hrights with ⟨⟨Hn1, Hn2, -⟩, ⟨Haddr, -⟩, -⟩
  ihave #Hprem' := Hprem0
  imodintro
  unfold putgetProgram
  wp_apply (github_com.mit_pdos.etcd_grove.examples.putget.wp_initialize' _
      github_com.mit_pdos.etcd_grove.examples.putget.getIsPkgInit_wf) $$ [Hown Hn1 Hn2]
    as ⟨_, #Hinit⟩
  · iframe Hown
    iunfold read.readRegPerm
    iframe
  have hM := putget.wp_Main (GF := putgetGF) n id bootLog Hbf (by rw [HT]; omega)
    (by rw [HN]; omega) (by rw [HN]; omega) Hck Haf Hbuq Hdbo Hms hAs
  wp_apply hM $$ [Haddr Htok]
  · iframe; iframe #
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial

/-
**`compactkv`** (the client's `kv.Compact`, 2026-11-01): putgetc's file, for putgetc under
compaction pressure (`common.StartCompactingServer`, revision mode, retention 1; five rounds of a
put of the round's key, a client compaction at the revision before it, a get of the key);
putgetc's and putget's history below is the originals'.

Lean-first (no Rocq counterpart).

# The adequacy example's closed theorem (item 9, stage 3, 2026-10-18)

A closed theorem about the operational semantics of `compactkv`'s program (`examples/compactkv`): the
package's initialization (which initializes its import closure: etcd's server, its gRPC layer,
the client, raft, ...) followed by `Main()` -- one etcd member started in process, a client, a
five rounds of a `Put` of the round's key with `v`, a `Compact` at the revision before it and a
`Get` of the key, each with a panic unless the `Get` returned `v` -- started from a
fresh state (no package initialized, one thread): for every real execution of `n` steps, the main
thread's result, if it has one, is `#()`, no thread is stuck, and no thread has ended in a panic.

It follows from `EtcdGrove.goose_adequacy_start` (through `common/Adequacy.lean`'s `etcd_adequate`) (`Proof/runtime/Start.lean`: Perennial's
`goose_adequacy` whose WP proof also receives program start's rights, D19d) with the read
package's two metric names and the client address `127.0.0.1:23794`, instantiated with the
trivial extension (`common/TrivialExt.lean`; the proofs are generic over the extensions) and a ghost-state bundle `compactkvGF`, from `compactkv`'s
`wp_initialize'` (`Init.lean`, over the program's package table `PkgTable.lean`) and
`compactkv_Main` (`Results.lean`).

**Its hypotheses** (D19a; `notes/decisions.md`, D19r):
* pure facts of the program and its environment: `BootFacts id bootLog` (the member id and the
  bootstrap log Go computes), `ckptEffectsOk`, `authRecordsFit`,
  `apply.backendUnderQuota`, `grpcRepliesFit` (the replies' encoded size, `grpc.start`'s, 2026-10-31),
  `storage.diskOk` (D22 S-j2), `namesUnclaimed`/`addrsUnclaimed` (D19d),
  and the execution's length (`n + 2 ≤ 2 ^ 28`: the thread bound and, with `N = n + 1`, the
  time-receipt bounds; `n + n + 7 ≤ backend.wbInit`: the backend's write-back budget `bootstrap`'s
  contract gives);
* the semantics: `go.Semantics`, the package assumptions (`compactkv`'s, the cache's), and the
  model classes the proofs take (`Float64ToInt64Semantics`, `DialWithBalancerBody`,
  `log.NewModel`; the method-set facts, `v3rpc.ServerMethodSets`, `errors.AsTarget` of
  `rpctypes.EtcdError`, `ErrorStringLeaf`, `RpctypesEtcdErrorMethods`, are theorems of the
  package assumptions), and `ContextReadErrs` (`context.Canceled`'s and `DeadlineExceeded`'s method
  facts from `context`'s package fact: the read package's initializer's premise class, item 8);
* triples of functions the program calls, with fresh resources (`compactkv.premises`: `bootstrap`'s
  contract, the raft wrapper's names-only contracts, `Stop` of a started node,
  `runsNoRequireLeader`), at every ghost-state instance;
* (until 2026-10-20 also two marked hypotheses, false under the then Perennial pin,
  `EofFromIoInit` and `ClosedchanFromContextInit`: `io.EOF` and `context`'s `closedchan` now come
  from their packages' facts, `v3rpc.eofVar_of_init` and `context.isClosedchanInit_of_init`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.compactkv.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.compactkv.PkgTable
public import Proof.runtime.Start
public import Proof.runtime.Threads
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.TrivialExt

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp

/-! ## The ghost-state bundle -/

/-- The functors (as the register's `registerGF`): the universal camera (`AllG`) at slot 0, then
invariants, later credits, GooseLang's heap, prophecies and package state. Every other slot is the unit functor. -/
def compactkvGF : BundledGFunctors := fun i =>
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
def compactkvGF_allG : AllG compactkvGF := ⟨⟨0, rfl⟩⟩

instance compactkvGF_gooseGpreS : GooseGpreS compactkvGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := ((), PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := compactkvGF_allG

/-- **A ghost-state instance at the local context `lctx`** (the hypotheses below are stated over
every instance of the ghost state whose Go local context is the semantics' own). -/
abbrev heapAtCkv (hG : HeapGS .hasLC compactkvGF) (lctx : GoLocalContext) : HeapGS .hasLC compactkvGF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- The program: `compactkv`'s initialization, then `Main()`. -/
def compactkvProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.compactkv.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.compactkv.Main) #()

/-- The read package's two metric names, which `compactkv`'s initialization registers (`readRegPerm`,
D16). -/
def compactkvNames : List GoString := [read.slowReadIndexName, read.readIndexFailedName]

/-- **The adequacy example is safe** (see the file header): every real execution of
`compactkvProgram` from a fresh state with one thread, of `n` steps: if the main thread has finished,
its result is `#()` (`Main` returned: each round's `Get` that returned `nil` returned its `Put`'s value); no
thread is stuck; no thread has ended in a panic. -/
theorem compactkv_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.compactkv.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC compactkvGF, ContextReadErrs (GF := compactkvGF) (hG := heapAtCkv hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC compactkvGF, ContextErrsClient (GF := compactkvGF) (hG := heapAtCkv hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : compactkv.BootFacts id ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed compactkvProgram compactkvNames)
    (HAs : addrsUnclaimed compactkvProgram [go!"127.0.0.1:23794"])
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC compactkvGF,
      ⊢ compactkv.premises (GF := compactkvGF) (hG := heapAtCkv hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([compactkvProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) (Hwb : n + n + 7 ≤ backend.wbInit) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  refine etcd_adequate (GF := compactkvGF) github_com.mit_pdos.etcd_grove.examples.compactkv.initialize'
    ((@! github_com.mit_pdos.etcd_grove.examples.compactkv.Main) #())
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) [go!"127.0.0.1:23794"] (by decide) σ g ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ Hlctx Hinit Hthreads HNs HAs
    n κs t2 σ2 Hsteps fun hG HN HT => ?_
  letI : HeapGS .hasLC compactkvGF := heapAtCkv hG lctx
  haveI := Hctx hG
  haveI := Hcec hG
  unfold progOk
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.compactkv.wp_initialize' _ github_com.mit_pdos.etcd_grove.examples.compactkv.getIsPkgInit_wf, ?_⟩
  ihave #Hprem' := Hprem hG
  iintro #Hinit Htok ⟨Has, -⟩
  icases BigSepL.bigSepL_cons.1 $$ Has with ⟨Haddr, -⟩
  have hM := compactkv.wp_Main (GF := compactkvGF) n id ctxs boot Hbf (by rw [HT]; omega)
    (by rw [HN]; omega) (by rw [HN]; omega) Hck Haf Hbuq Hrf Hdbo inferInstance EtcdGrove.rpctypesEtcdError_asTarget
  wp_apply hM $$ [Haddr Htok]
  · iframe; iframe #
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial

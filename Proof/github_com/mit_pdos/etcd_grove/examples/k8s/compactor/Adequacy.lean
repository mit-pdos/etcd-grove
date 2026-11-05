/-
Lean-first (no Rocq counterpart).

# Kubernetes' compactor example's closed theorem (K4 of `notes/k8s-compactor-plan.md`)

A closed theorem about the operational semantics of `examples/k8s/compactor`'s program: the
package's initialization followed by `Main()` (one etcd member started in process in compaction mode
with etcd's compactor off, `ListFromCacheSnapshot` off, a writer, three API servers each running
Kubernetes' compactor and checking it), started from a fresh state: for every real execution of `n`
steps, the main thread's result, if it has one, is `#()`, no thread is stuck, and no thread has ended
in a panic. So no API server's check panics: `CompactRevision` never decreases, it is at most a
later read's revision, and `compact_rev_key` holds a revision at most a later read's; and no
compactor round panics (the missing-key panic, `issues/k8s-apiserver-compactor-missing-key-panic.md`,
does not happen: nothing deletes the key).

As `compactwatch`'s (`examples/etcd/compactwatch/Adequacy.lean`, whose header lists the hypotheses'
kinds, D19a), at this program's configuration (`etcdstart.premises` at member `k8scompactor`, its two
addresses), with one more named hypothesis: `clock.RealClock.After`'s contract (`time.After(d)`
returns a channel some time is sent on), which the compactor's loop waits on (client-go's results
take it too).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.PkgTable
public import Proof.runtime.Start
public import Proof.runtime.Threads
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TrivialExt

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

/-! ## The ghost-state bundle -/

/-- The functors (as the register's `registerGF`): the universal camera (`AllG`) at slot 0, then
invariants, later credits, GooseLang's heap, prophecies and package state. Every other slot is the unit functor. -/
def k8scompactorGF : BundledGFunctors := fun i =>
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
def k8scompactorGF_allG : AllG k8scompactorGF := ⟨⟨0, rfl⟩⟩

instance k8scompactorGF_gooseGpreS : GooseGpreS k8scompactorGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨k8scompactorGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := k8scompactorGF_allG

/-- **A ghost-state instance at the local context `lctx`** (the hypotheses below are stated over
every instance of the ghost state whose Go local context is the semantics' own). -/
abbrev heapAtKc (hG : HeapGS .hasLC k8scompactorGF) (lctx : GoLocalContext) : HeapGS .hasLC k8scompactorGF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- The program: the compactor example's initialization, then `Main()`. -/
def k8scompactorProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.k8s.compactor.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Main) #()

/-- The read package's two metric names, which the example's initialization registers
(`readRegPerm`, D16). -/
def k8scompactorNames : List GoString := [read.slowReadIndexName, read.readIndexFailedName]

/-- **The compactor example is safe** (see the file header): every real execution of
`k8scompactorProgram` from a fresh state with one thread, of `n` steps: if the main thread has
finished, its result is `#()`; no thread is stuck; no thread has ended in a panic (no API server's
check panics, no compactor round panics). -/
theorem k8s_compactor_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8scompactorGF, ContextReadErrs (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC k8scompactorGF, ContextErrsClient (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcdstart.BootFacts id ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed k8scompactorProgram k8scompactorNames)
    (HAs : addrsUnclaimed k8scompactorProgram [go!"127.0.0.1:23976"])
    -- (2026-11-03, the WAL's API, change 6) the member's WAL directory holds no WAL at start
    (HDs : walDirsAbsent k8scompactorProgram [config.walDirOf go!"k8scompactor.etcd" go!""])
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC k8scompactorGF,
      ⊢ etcdstart.premises (GF := k8scompactorGF) (hG := heapAtKc hG lctx) go!"k8scompactor"
        go!"127.0.0.1:23986" go!"127.0.0.1:23976" n id ctxs boot)
    -- the named hypothesis of `clock.RealClock.After` (`time.After(d)`), as in client-go's link
    (Hafter : ∀ hG : HeapGS .hasLC k8scompactorGF,
      EtcdGrove.clock.RealClock.After.spec (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([k8scompactorProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  refine etcd_adequate (GF := k8scompactorGF) github_com.mit_pdos.etcd_grove.examples.k8s.compactor.initialize'
    ((@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Main) #())
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) [go!"127.0.0.1:23976"] (by decide) [config.walDirOf go!"k8scompactor.etcd" go!""] (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩) σ g ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ Hlctx Hinit Hthreads HNs HAs HDs
    n κs t2 σ2 Hsteps fun hG HN HT => ?_
  letI : HeapGS .hasLC k8scompactorGF := heapAtKc hG lctx
  -- (Q1 (c), 2026-11-05) the compactor registry's name (`etcd3`'s package fact): the program
  -- registers no compactor (`StartCompactorPerEndpoint` is not called), so any name will do
  letI : EtcdGrove.k8s.CompactorRegistry := ⟨0⟩
  haveI := Hctx hG
  haveI := Hcec hG
  unfold progOk
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.k8s.compactor.wp_initialize' _ github_com.mit_pdos.etcd_grove.examples.k8s.compactor.getIsPkgInit_wf, ?_⟩
  ihave #Hprem' := Hprem hG
  iintro #Hinit Htok ⟨Has, -, Hds⟩
  icases BigSepL.bigSepL_cons.1 $$ Hds with ⟨Hwd, -⟩
  icases BigSepL.bigSepL_cons.1 $$ Has with ⟨Haddr, -⟩
  have hM := k8s_compactor.wp_Main (GF := k8scompactorGF) (Hafter hG) n id ctxs boot Hbf (by rw [HT]; omega)
    (by rw [HN]; omega) (by rw [HN]; omega) (by unfold bootWB backend.wbInit; omega) Hck Haf Hbuq Hrf Hdbo inferInstance EtcdGrove.rpctypesEtcdError_asTarget
  wp_apply hM $$ [Haddr Htok Hwd]
  · iframe; iframe #
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial

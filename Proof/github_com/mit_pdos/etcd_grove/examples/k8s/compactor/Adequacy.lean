/-
Lean-first (no Rocq counterpart).

# Kubernetes' compactor example's closed theorem (K4 of `notes/k8s-compactor-plan.md`)

A closed theorem about the operational semantics of `examples/k8s/compactor`'s program: the
package's initialization followed by `Main()` (one etcd member started in process in compaction mode
with etcd's compactor off, a writer, five API servers checking Kubernetes' compactor: three each
with its own (`NewCompactor`), two sharing the process's (`StartCompactorPerEndpoint`)), started
from a fresh state: for every real execution of `n`
steps, the main thread's result, if it has one, is `#()`, no thread is stuck, and no thread has ended
in a panic. So no API server's check panics: `CompactRevision` never decreases, it is at most a
later read's revision, and `compact_rev_key` holds a revision at most a later read's; and no
compactor round panics (the missing-key panic, `issues/k8s-apiserver-compactor-missing-key-panic.md`,
does not happen: nothing deletes the key).

As `compactwatch`'s (`examples/etcd/compactwatch/Adequacy.lean`, whose header lists the hypotheses'
kinds, D19a), at this program's configuration (`etcdstart.premises` at member `k8scompactor`, its two
addresses), with one more named hypothesis: `clock.RealClock.After`'s contract (`time.After(d)`
returns a channel some time is sent on), which the compactor's loop waits on (client-go's results
take it too). The compactor registry (`etcd3`'s package fact, Q1 (c)) is allocated before the
program's proof is chosen (`etcd_adequate_alloc`): its name instantiates `k8s.CompactorRegistry`,
and `Main` receives the claims' authority (`regAuth ∅`).

**Three members under partitions** (K6, 2026-11-05; `k8s_compactor_partition_adequate`): the same
guarantee for the example's initialization followed by `MainPartition(sched)`, the schedule built
as a slice literal (`schedLit`, as `examples/etcd/partition`'s), for *every* list of steps (its
length below `2^63`, a Go slice's bound): three members started in process in compaction mode
(`cluster3.StartCluster` at `clusterCfg`), a bridge to each, the partitioner on the schedule, the
writer and the five API servers each with a client of the three bridges. Its hypotheses are
`examples/etcd/partition`'s at `clusterCfg` (the member ids and bootstrap log, `cluster3.BootFacts`;
the nine addresses unclaimed; the three data directories distinct and fresh; `cluster3.premises`)
with this example's (`clock.RealClock.After`, the registry allocated as above).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AdequacyMembers
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.PkgTable
public import Proof.runtime.Start
public import Proof.runtime.Threads
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.TrivialExt
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.SchedLit

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
    -- (2026-11-03, the WAL's API, change 6; sweep repairs 1, W3/W4) the member's data directory, fresh at start (`dataDirsAbsent`)
    (HDs : dataDirsAbsent k8scompactorProgram [go!"k8scompactor.etcd"])
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    (HEnv : verifyEnvOff k8scompactorProgram)
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
  refine etcd_adequate_alloc_members (GF := k8scompactorGF) (hAsLit := by decide) (HEnv := HEnv) github_com.mit_pdos.etcd_grove.examples.k8s.compactor.initialize'
    ((@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Main) #())
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) [go!"127.0.0.1:23976"] (by decide) [go!"k8scompactor.etcd"] (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩)
    -- (hub step 7) the one member's start bundle: its client address, its data directory
    [(k8s_compactor.memberName, ⟨none, some k8s_compactor.clientAddr⟩)] [] (List.Perm.refl _)
    (List.Perm.refl _) σ g ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ Hlctx Hinit Hthreads HNs HAs HDs
    n κs t2 σ2 Hsteps fun hG HN HT => ?_
  letI : HeapGS .hasLC k8scompactorGF := heapAtKc hG lctx
  -- (Q1 (c), C3, 2026-11-05) the compactor registry, allocated before the program's proof is
  -- chosen: its name instantiates the class (`etcd3`'s package fact is the registry at that name),
  -- and `Main` receives the claims' authority, with no endpoint claimed
  refine ⟨GName, fun γ => EtcdGrove.k8s.regAuth (reg := ⟨γ⟩) (∅ : GMap GoString GName),
    EtcdGrove.k8s.regAuth_alloc, fun γ => ?_⟩
  letI : EtcdGrove.k8s.CompactorRegistry := ⟨γ⟩
  haveI := Hctx hG
  haveI := Hcec hG
  unfold progOk
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.k8s.compactor.wp_initialize' _ github_com.mit_pdos.etcd_grove.examples.k8s.compactor.getIsPkgInit_wf, ?_⟩
  ihave #Hprem' := Hprem hG
  iintro #Hinit Htok ⟨⟨Hms, -⟩, Hreg⟩
  icases BigSepL.bigSepL_cons.1 $$ Hms with ⟨Hstart, -⟩
  have hM := k8s_compactor.wp_Main (GF := k8scompactorGF) (Hafter hG) n id ctxs boot Hbf (by rw [HT]; word)
    (by rw [HN]; omega) (by rw [HN]; omega) (by unfold bootWB backend.wbInit; omega) Hck Haf Hbuq Hrf Hdbo inferInstance EtcdGrove.rpctypesEtcdError_asTarget
  wp_apply hM $$ [Hstart Htok Hreg]
  · iframe; iframe #
  ipureintro
  rfl

/-- The program with three members: the compactor example's initialization, then
`MainPartition(sched)` with the schedule built as a slice literal. -/
def k8scompactorPProgram [GoSemanticsFunctions]
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.k8s.compactor.initialize' #() ;;
  App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.MainPartition)) (schedLit steps)

/-- The program's addresses: the three members' peer addresses, their client addresses, and the
bridges' addresses (`clusterCfg`'s). -/
def k8scompactorPAddrs : List GoString :=
  [k8s_compactor.clusterCfg.Peer1', k8s_compactor.clusterCfg.Peer2', k8s_compactor.clusterCfg.Peer3',
    k8s_compactor.clusterCfg.Client1', k8s_compactor.clusterCfg.Client2',
    k8s_compactor.clusterCfg.Client3',
    k8s_compactor.clusterCfg.Bridge1', k8s_compactor.clusterCfg.Bridge2',
    k8s_compactor.clusterCfg.Bridge3']

/-- The members' data directories `<name>.etcd` (sweep repairs 1, W3/W4: until then their WAL directories). -/
def k8scompactorPDataDirs : List GoString :=
  [(k8s_compactor.clusterCfg.Name1' ++ go!".etcd"),
    (k8s_compactor.clusterCfg.Name2' ++ go!".etcd"),
    (k8s_compactor.clusterCfg.Name3' ++ go!".etcd")]

/-- **The compactor example on three members under partitions is safe** (see the file header):
every real execution of `k8scompactorPProgram steps` from a fresh state with one thread, of `n`
steps: if the main thread has finished, its result is `#()`; no thread is stuck; no thread has
ended in a panic (no API server's check panics, no compactor round panics). -/
theorem k8s_compactor_partition_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8scompactorGF, ContextReadErrs (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC k8scompactorGF, ContextErrsClient (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : cluster3.BootFacts id₁ id₂ id₃ ps ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps : steps.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (k8scompactorPProgram steps) k8scompactorNames)
    (HAs : addrsUnclaimed (k8scompactorPProgram steps) k8scompactorPAddrs)
    -- (2026-11-03, the WAL's API, change 6; sweep repairs 1, W3/W4) the members' data directories,
    -- fresh at start (`dataDirsAbsent`; their distinctness is now `decide`d, no longer a hypothesis)
    (HDs : dataDirsAbsent (k8scompactorPProgram steps) k8scompactorPDataDirs)
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    (HEnv : verifyEnvOff (k8scompactorPProgram steps))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC k8scompactorGF,
      ⊢ cluster3.premises (GF := k8scompactorGF) (hG := heapAtKc hG lctx) k8s_compactor.clusterCfg n
        id₁ id₂ id₃ ps ctxs boot)
    -- the named hypothesis of `clock.RealClock.After` (`time.After(d)`), as in client-go's link
    (Hafter : ∀ hG : HeapGS .hasLC k8scompactorGF,
      EtcdGrove.clock.RealClock.After.spec (GF := k8scompactorGF) (hG := heapAtKc hG lctx))
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNsteps n ([k8scompactorPProgram steps], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  refine etcd_adequate_alloc_members (GF := k8scompactorGF) (hAsLit := by decide) (HEnv := HEnv)
    github_com.mit_pdos.etcd_grove.examples.k8s.compactor.initialize'
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.compactor.MainPartition)) (schedLit steps))
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) k8scompactorPAddrs (by decide)
    k8scompactorPDataDirs (by decide)
    -- (hub step 7's A3) the cluster's members and its bridges; the program's address list is theirs
    -- up to order (peers, then clients, then bridges)
    (cluster3.members k8s_compactor.clusterCfg) (cluster3.bridges k8s_compactor.clusterCfg) (by decide) (List.Perm.refl _) σ g ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ Hlctx Hinit Hthreads HNs
    HAs HDs n κs t2 σ2 Hsteps' fun hG HN HT => ?_
  letI : HeapGS .hasLC k8scompactorGF := heapAtKc hG lctx
  -- the compactor registry, allocated before the program's proof is chosen (as `k8s_compactor_adequate`)
  refine ⟨GName, fun γ => EtcdGrove.k8s.regAuth (reg := ⟨γ⟩) (∅ : GMap GoString GName),
    EtcdGrove.k8s.regAuth_alloc, fun γ => ?_⟩
  letI : EtcdGrove.k8s.CompactorRegistry := ⟨γ⟩
  haveI := Hctx hG
  haveI := Hcec hG
  unfold progOk
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.k8s.compactor.wp_initialize' _ github_com.mit_pdos.etcd_grove.examples.k8s.compactor.getIsPkgInit_wf, ?_⟩
  ihave #Hprem' := Hprem hG
  iintro #Hinit Htok ⟨Hres, Hreg⟩
  ihave Hstart := cluster3.startRes_intro k8s_compactor.clusterCfg $$ Hres
  -- the schedule's slice literal (as `etcd_partition_adequate`)
  wp_bind (schedLit steps)
  unfold schedLit
  iapply (wp_slice_literal (V := github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) (l := steps)
    (kvs := steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty)))
  have hp := pure_wp_array_lit_full (hlc := HasLC.hasLC) (GF := k8scompactorGF)
    (go.arrayLiteralSize
      (steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty)))
    github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty steps _ rfl
    (by rw [arrayLiteralSize_vals]; simp)
    (by rw [arrayLiteralSize_vals]; simpa using Hsteps)
  have hp' : ∀ Ψ : val → IProp k8scompactorGF,
      iprop(▷ (£ 1 -∗ WP (Val #(array.mk
          (go.arrayLiteralSize
            (steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty)))
          steps)) {{ Ψ }})) ⊢
        WP (App (Val (GoInstruction (CompositeLiteral (go.ArrayType
            (go.arrayLiteralSize
              (steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty)))
            github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty))))
          (Val (LiteralValueV
            (steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty)))))
          {{ Ψ }} :=
    fun Ψ => hp.pure_wp_wp _ _ Ψ [] trivial
  iapply (hp' _)
  inext
  iintro -
  wp_auto
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  imod ownSlice_persist _ _ _ $$ Hsl with #Hsl
  (try wp_auto)
  have hM := k8s_compactor.wp_MainPartition (GF := k8scompactorGF) (Hafter hG) n id₁ id₂ id₃ ps ctxs
    boot
    (slice.mk sl
      (W64 (go.arrayLiteralSize
        (steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty))))
      (W64 (go.arrayLiteralSize
        (steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty)))))
    steps Hbf
    (by rw [HT]; word) (by rw [HN]; omega) (by rw [HN]; omega) (by unfold bootWB backend.wbInit; omega)
    Hck Haf Hbuq Hrf Hdbo inferInstance EtcdGrove.rpctypesEtcdError_asTarget
  wp_apply hM $$ [Hstart Htok Hreg]
  · iframe; iframe #
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial

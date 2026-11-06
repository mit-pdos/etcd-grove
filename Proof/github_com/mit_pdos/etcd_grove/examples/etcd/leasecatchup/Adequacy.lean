/- Lean-first (no Rocq counterpart).

# The multi-member lease example's closed theorem (lease-mono3 step 1, 2026-11-06, `notes/lease-mono3-plan.md`, Scope §3)

A closed theorem about the operational semantics of `leasecatchup`'s program
(`examples/etcd/leasecatchup`): the package's initialization followed by `Main()` -- three etcd
members started in process (`cluster3.StartCluster` at `clusterCfg`, in the monotone lease mode,
snapshots every applied entry and the log compacted right below them), a bridge to each, a lease
granted through member 3, member 3 cut off the two others while up to 20 fillers are granted through
member 1, the links mended, member 3's listing polled until it lists the last filler, and a panic
unless that listing also lists the lease granted through member 3 -- started from a fresh state (no
package initialized, one thread): for every real execution of `n` steps, the main thread's result,
if it has one, is `#()`, no thread is stuck, and no thread has ended in a panic.

As `examples/etcd/partition`'s and `k8s_compactor_partition_adequate`'s (`etcd_adequate_members`
with the cluster's members and its bridges, hub step 7's A3), at this program's configuration,
with leasegrant's lease hypotheses: `leasePeersOk` (the peers answer the lease handler's path as
etcd's lease handler does) and `lease.leasesNoExpiry` (no lease the cluster grants expires during
the run: the leases are granted for an hour, the run takes seconds; Scope §2's time budget).

**What is new** over leasegrant's theorem: a configuration in which the leased restore actually
happens in Go (`examples/etcd/leasecatchup/leasecatchup_test.go` counts, in every run, a merged
snapshot sent to member 3, applied, and its lessor recovered from the snapshot's lease bucket),
so that the guarantee covers a member whose lessor is rebuilt by `Recover` from a snapshot: member
3's listing still lists the lease granted through it (the monotone lessor's `Recover` premise,
S2–S4's, proved inside the server's apply loop). The proof of `Main` itself does not reason about
the catch-up.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AdequacyMembers
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.PkgTable
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
def leasecatchupGF : BundledGFunctors := fun i =>
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
def leasecatchupGF_allG : AllG leasecatchupGF := ⟨⟨0, rfl⟩⟩

instance leasecatchupGF_gooseGpreS : GooseGpreS leasecatchupGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨leasecatchupGF_allG⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨7, rfl⟩⟩
  goosePreGAllG := leasecatchupGF_allG

/-- **A ghost-state instance at the local context `lctx`** (the hypotheses below are stated over
every instance of the ghost state whose Go local context is the semantics' own). -/
abbrev heapAtLcu (hG : HeapGS .hasLC leasecatchupGF) (lctx : GoLocalContext) :
    HeapGS .hasLC leasecatchupGF :=
  ⟨hG.goose_globalGS, { hG.goose_localGS with goose_go_local_context := lctx }⟩

/-! ## The closed theorem -/

section adequacy
variable [go_gctx : GoGlobalContext]

/-- The program: `leasecatchup`'s initialization, then `Main()`. -/
def leasecatchupProgram [GoSemanticsFunctions] : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.initialize' #() ;;
  (@! github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Main) #()

/-- The read package's two metric names, which `leasecatchup`'s initialization registers
(`readRegPerm`, D16). -/
def leasecatchupNames : List GoString := [read.slowReadIndexName, read.readIndexFailedName]

/-- The program's addresses: the three members' peer addresses, their client addresses, and the
bridges' addresses (`clusterCfg`'s). -/
def leasecatchupAddrs : List GoString :=
  [etcd_leasecatchup.clusterCfg.Peer1', etcd_leasecatchup.clusterCfg.Peer2',
    etcd_leasecatchup.clusterCfg.Peer3',
    etcd_leasecatchup.clusterCfg.Client1', etcd_leasecatchup.clusterCfg.Client2',
    etcd_leasecatchup.clusterCfg.Client3',
    etcd_leasecatchup.clusterCfg.Bridge1', etcd_leasecatchup.clusterCfg.Bridge2',
    etcd_leasecatchup.clusterCfg.Bridge3']

/-- The members' WAL directories (`WALDir()` of their data directories `<name>.etcd`). -/
def leasecatchupWalDirs : List GoString :=
  [config.walDirOf (etcd_leasecatchup.clusterCfg.Name1' ++ go!".etcd") go!"",
    config.walDirOf (etcd_leasecatchup.clusterCfg.Name2' ++ go!".etcd") go!"",
    config.walDirOf (etcd_leasecatchup.clusterCfg.Name3' ++ go!".etcd") go!""]

/-- **The multi-member lease example is safe** (see the file header): every real execution of
`leasecatchupProgram` from a fresh state with one thread, of `n` steps: if the main thread has
finished, its result is `#()`; no thread is stuck; no thread has ended in a panic (member 3, once
caught up by a snapshot, still lists the lease granted through it). -/
theorem etcd_leasecatchup_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC leasecatchupGF,
      ContextReadErrs (GF := leasecatchupGF) (hG := heapAtLcu hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC leasecatchupGF,
      ContextErrsClient (GF := leasecatchupGF) (hG := heapAtLcu hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : cluster3.BootFacts id₁ id₂ id₃ ps ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit) (Hbuq : apply.backendUnderQuota)
    (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (Hlp : leasePeersOk) (Hlne : lease.leasesNoExpiry)
    (HNs : prometheus.namesUnclaimed leasecatchupProgram leasecatchupNames)
    (HAs : addrsUnclaimed leasecatchupProgram leasecatchupAddrs)
    -- the members' WAL directories, distinct (`filepath.Join` is opaque here), hold no WAL at start
    (HDsNd : leasecatchupWalDirs.Nodup)
    (HDs : walDirsAbsent leasecatchupProgram leasecatchupWalDirs)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC leasecatchupGF,
      ⊢ cluster3.premises (GF := leasecatchupGF) (hG := heapAtLcu hG lctx)
          etcd_leasecatchup.clusterCfg n id₁ id₂ id₃ ps ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([leasecatchupProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  refine etcd_adequate_members (GF := leasecatchupGF)
    github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.initialize'
    ((@! github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Main) #())
    (fun v => v = #()) (fun p h => intoVal_ne_PanicV () p h.symm) leasecatchupAddrs (by decide)
    leasecatchupWalDirs HDsNd
    -- (hub step 7's A3) the cluster's members and its bridges; the program's address list is theirs
    -- up to order (peers, then clients, then bridges)
    (cluster3.members etcd_leasecatchup.clusterCfg) (cluster3.bridges etcd_leasecatchup.clusterCfg)
    (by decide) (List.Perm.refl _) σ g ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ Hlctx Hinit Hthreads
    HNs HAs HDs n κs t2 σ2 Hsteps fun hG HN HT => ?_
  letI : HeapGS .hasLC leasecatchupGF := heapAtLcu hG lctx
  haveI := Hctx hG
  haveI := Hcec hG
  unfold progOk
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.wp_initialize' _
    github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.getIsPkgInit_wf, ?_⟩
  ihave #Hprem' := Hprem hG
  iintro #Hinit Htok Hres
  ihave Hstart := cluster3.startRes_intro etcd_leasecatchup.clusterCfg $$ Hres
  have hM := etcd_leasecatchup.wp_Main (GF := leasecatchupGF) n id₁ id₂ id₃ ps ctxs boot Hbf
    (by rw [HT]; omega) (by rw [HN]; omega) (by rw [HN]; omega)
    (by unfold bootWB backend.wbInit; omega) Hck Haf Hbuq Hrf Hdbo Hlp Hlne inferInstance
    EtcdGrove.rpctypesEtcdError_asTarget
  wp_apply hM $$ [Hstart Htok]
  · iframe; iframe #
  ipureintro
  rfl

end adequacy

end EtcdGrove
end Perennial

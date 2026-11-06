/- Lean-first (no Rocq counterpart).

# The watch run's closed theorem (W4e of `notes/watch-cut-plan.md`, 2026-10-22)

watchkv's closed theorem (`watchkv/Adequacy.lean`) for linkv3p's cluster under partitions: the
package's initialization followed by `MainWatch(nw, nops, sched)` -- the writers' puts picked, the
cluster started (`startCluster`: three members, a bridge to each, three clients each of every
bridge), a prefix watch on `wk/` from revision `1` through the first client, the partitioner forked
on the schedule `sched` (any list of steps, built as a slice literal, `schedLit`: the links between
members cut and mended, the links between each client and its member blackholed, unblackholed or
dropped), `nw` writers of `nops` puts each through clients picked at random, the watch read up to
the highest successful put's revision and checked against the writes (a panic if it did not report
exactly the writes: every put at revisions `2, 3, ...`, no gap or repeat, each attempted, each
successful put at its revision) -- started from a fresh state (no package initialized, one thread):
for every real execution of `n` steps, the main thread's result, if it has one, is `WatchOk`,
`WatchFailed` or `WatchEnded`, no thread is stuck, and no thread has ended in a panic. The watch
resumes across members (the client watcher's reconnection, at any member of its connection, D32)
and its events are the cluster's committed history's (`etcdModelOfHistory`).

It follows, as `etcd_partition_adequate`, from `EtcdGrove.goose_adequacy_start` (through `common/Adequacy.lean`'s `etcd_adequate`) with the read package's
two metric names and the nine addresses, over linkv's ghost-state bundle `linkvGF`, from
`linkv3p`'s `wp_initialize'` and `etcd_partition.wp_MainWatch` (`Link.lean`).

**Its hypotheses** are `etcd_partition_adequate`'s, but `Run`'s bounds on `clients` and `ops`, plus the
client watcher's (watchkv's `watch_adequate`: the class premises and `ContextErrsClient`) and
watchkv's bounds on `nw` and `nops`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.AdequacyMembers
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartRes
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Adequacy

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3

attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt

section adequacy
variable [go_gctx : GoGlobalContext]

/-- The watch run: `linkv3p`'s initialization, then `MainWatch(nw, nops, sched)` with the schedule
built as a slice literal. -/
def linkv3pWatchProgram [GoSemanticsFunctions] (nw nops : w64)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) : Expr :=
  github_com.mit_pdos.etcd_grove.examples.etcd.partition.initialize' #() ;;
  App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.partition.MainWatch)) (Val #nw))
    (Val #nops)) (schedLit steps)

/-- **The watch run over the partitioned cluster is safe** (see the file header): every real
execution of `linkv3pWatchProgram nw nops steps` from a fresh state with one thread, of `n` steps:
if the main thread has finished, its result is `WatchOk`, `WatchFailed` or `WatchEnded`; no thread
is stuck; no thread has ended in a panic. -/
theorem etcd_partition_watch_adequate [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.partition.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    -- (2026-10-24, rafthttp stage 6d) `*peer` implements `Pausable` (the partitioner's `CutPeer`)
    (Hctx : ∀ hG : HeapGS .hasLC linkvGF, ContextReadErrs (GF := linkvGF) (hG := linkvHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC linkvGF,
      ContextErrsClient (GF := linkvGF) (hG := linkvHeapAt hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_partition.BootFacts id₁ id₂ id₃ ps ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (nw nops : w64)
    (H0 : 0 ≤ sint.Z nw) (H31 : sint.Z nw < 2 ^ 31) (Hops : 0 ≤ sint.Z nops)
    (Hmul : sint.Z nw * sint.Z nops < 2 ^ 62)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps : steps.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (linkv3pWatchProgram nw nops steps) linkv3pNames)
    (HAs : addrsUnclaimed (linkv3pWatchProgram nw nops steps) linkv3pAddrs)
    -- (2026-11-03, the WAL's API, change 6) the members' WAL directories, distinct (`WALDir()` of
    -- the members' distinct data directories: `filepath.Join` is opaque here), hold no WAL at start
    (HDsNd : [config.walDirOf (etcd_partition.name₁ ++ go!".etcd") go!"", config.walDirOf (etcd_partition.name₂ ++ go!".etcd") go!"", config.walDirOf (etcd_partition.name₃ ++ go!".etcd") go!""].Nodup)
    (HDs : walDirsAbsent (linkv3pWatchProgram nw nops steps) [config.walDirOf (etcd_partition.name₁ ++ go!".etcd") go!"", config.walDirOf (etcd_partition.name₂ ++ go!".etcd") go!"", config.walDirOf (etcd_partition.name₃ ++ go!".etcd") go!""])
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC linkvGF,
      ⊢ etcd_partition.premises (GF := linkvGF) (hG := linkvHeapAt hG lctx) n id₁ id₂ id₃ ps ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNsteps n ([linkv3pWatchProgram nw nops steps], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(W64 0) ∨ v = #(W64 1) ∨ v = #(W64 2)) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  refine etcd_adequate_members (GF := linkvGF) github_com.mit_pdos.etcd_grove.examples.etcd.partition.initialize'
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.partition.MainWatch)) (Val #nw))
      (Val #nops)) (schedLit steps))
    (fun v => v = #(W64 0) ∨ v = #(W64 1) ∨ v = #(W64 2)) (fun p h => h.elim (fun h => intoVal_ne_PanicV _ p h.symm)
      (fun h => h.elim (fun h => intoVal_ne_PanicV _ p h.symm)
        (fun h => intoVal_ne_PanicV _ p h.symm))) linkv3pAddrs (by decide) [config.walDirOf (etcd_partition.name₁ ++ go!".etcd") go!"", config.walDirOf (etcd_partition.name₂ ++ go!".etcd") go!"", config.walDirOf (etcd_partition.name₃ ++ go!".etcd") go!""] HDsNd
    -- (hub step 7's A3) the cluster's members and its bridges; the program's address list is theirs
    -- up to order (peers, then clients, then bridges)
    (cluster3.members etcd_partition.clusterCfg) (cluster3.bridges etcd_partition.clusterCfg) (by decide) (List.Perm.refl _) σ g ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ Hlctx Hinit Hthreads HNs HAs HDs
    n κs t2 σ2 Hsteps' fun hG HN HT => ?_
  letI : HeapGS .hasLC linkvGF := linkvHeapAt hG lctx
  haveI := Hctx hG
  haveI := Hcec hG
  unfold progOk
  refine ⟨_, _, github_com.mit_pdos.etcd_grove.examples.etcd.partition.wp_initialize' _ github_com.mit_pdos.etcd_grove.examples.etcd.partition.getIsPkgInit_wf, ?_⟩
  ihave #Hprem' := Hprem hG
  iintro #Hinit Htok Hres
  ihave Hstart := cluster3.startRes_intro etcd_partition.clusterCfg $$ Hres
  -- the schedule's slice literal: the array of an abstract list takes one pure step
  -- (`pure_wp_array_lit_full`, before the generic automation unfolds it), then the slice over it
  -- (`wp_slice_literal`)
  wp_bind (schedLit steps)
  unfold schedLit
  iapply (wp_slice_literal (V := github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step) (l := steps)
    (kvs := steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty)))
  have hp := pure_wp_array_lit_full (hlc := HasLC.hasLC) (GF := linkvGF)
    (go.arrayLiteralSize
      (steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty)))
    github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty steps _ rfl
    (by rw [arrayLiteralSize_vals]; simp)
    (by rw [arrayLiteralSize_vals]; simpa using Hsteps)
  have hp' : ∀ Ψ : val → IProp linkvGF,
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
  have hM := etcd_partition.wp_MainWatch (GF := linkvGF) n id₁ id₂ id₃ ps ctxs boot nw nops
    (slice.mk sl
      (W64 (go.arrayLiteralSize
        (steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty))))
      (W64 (go.arrayLiteralSize
        (steps.map (arrayLitKE github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step.ty)))))
    steps Hbf
    (by rw [HT]; word) (by rw [HN]; omega) (by rw [HN]; omega) (by unfold bootWB backend.wbInit; omega) Hck Haf Hbuq Hrf Hdbo inferInstance EtcdGrove.rpctypesEtcdError_asTarget
    H0 H31 Hops Hmul
  wp_apply hM $$ [Hstart Htok]
  · iframe; iframe #
  iintro %r %Hr
  ipureintro
  rcases Hr with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)


end adequacy

end EtcdGrove
end Perennial

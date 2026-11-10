/-
The Kubernetes etcd3 store's linearizability instance's results
(`examples/k8s/etcd3/k8s_etcd3.go`; stage 6g of `notes/k8s-etcd3-plan.md`), restated, with the
trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`k8setcd3_Main`** (`Link.lean`'s `k8s_etcd3.wp_Main`): `Main(clients, ops)` -- one etcd member
  started in process, a kubernetes client configured for one attempt per call, the seed objects,
  the Kubernetes etcd3 store over the client (`etcd3.New`, the driver's codec, versioner,
  transformer and decoder), `Check(s, st0, clients, ops, 0)` (`lintest.Run` with the driver's Go
  model of the store, `Apply` over the store: `Create`, `Get`, `Delete`, `GuaranteedUpdate`, and
  `GetList` (paginated, with selectors and the past-revision modes; stage 7e);
  porcupine's checker), and a panic if porcupine answers `Illegal` -- does not panic and returns
  `Ok` or `Unknown`. From `isPkgInit k8setcd3`, the right to listen on `127.0.0.1:23896`, the main
  thread's token and `Main`'s named premises
  (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/Main.lean`), at the context errors'
  premise `ContextReadErrs` (k8s etcd3 7c-2 part 2, S7: the compactor's channel context's errors'
  descriptions; `k8s_etcd3_safe` already took it, `Hctx`).
* **`k8s_etcd3_safe`** (`Adequacy.lean`'s `k8s_etcd3_adequate`): the closed theorem. Every real
  execution of `n` steps of `k8setcd3`'s initialization followed by `Main(clients, ops)`, from a
  fresh state with one thread, has no stuck thread, no thread ended in a panic (so never
  "k8setcd3: porcupine found the history not linearizable"), and the main thread's result, if
  any, is `Ok` or `Unknown`; under k8setcd3's hypotheses at k8setcd3's configuration, the
  Kubernetes packages' semantics assumptions (the method-set facts `objTyOk` and
  `storageErrTyOk` follow from them).
* **`k8setcd3_MainCluster`** (`MainLinked.lean`'s `k8s_etcd3.wp_MainCluster`; step 1 of "k8s etcd3
  over cluster3" in `notes/k8s-etcd3-plan.md`, 2026-11-06): `MainCluster(clients, ops)` -- `Main`
  over a three-member cluster (`cluster3`, the client of its three bridges with etcd's default
  retries) -- does not panic and returns `Ok` or `Unknown`
  (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/MainCluster.lean`).
* **`k8s_etcd3_cluster_safe`** (`Adequacy.lean`'s `k8s_etcd3_cluster_adequate`): its closed
  theorem, `k8s_etcd3_safe`'s conclusion for `MainCluster(clients, ops)`, under the cluster's
  hypotheses (its boot facts and premises at `clusterCfg`, its nine addresses unclaimed, its three
  data directories distinct and fresh) for the one member's.
* **`k8setcd3_MainPartition`** (`MainLinked.lean`'s `k8s_etcd3.wp_MainPartition`; step 2 of "k8s
  etcd3 over cluster3", 2026-11-07): `MainPartition(clients, ops, sched)` -- `MainCluster` with
  `cluster3.Partitioner` running the schedule (peer cuts and mends, a bridge blackholed or
  unblackholed, its connections dropped) while `Check`'s clients run -- does not panic and returns
  `Ok` or `Unknown`, for every schedule
  (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/MainPartition.lean`).
* **`k8s_etcd3_partition_safe`** (`Adequacy.lean`'s `k8s_etcd3_partition_adequate`): its closed
  theorem, `k8s_etcd3_cluster_safe`'s conclusion for `MainPartition(clients, ops, sched)` with the
  schedule `steps` built as a slice literal (`schedLit`), for every `steps` of fewer than `2 ^ 63`
  steps, under `k8s_etcd3_cluster_safe`'s hypotheses.

**Pending hypotheses (k8s 7e-4, 2026-11-10).** Until 7e-1 lands, every result here takes the
client's `List` spec (`HList`; the store's `GetList` reads through it) as a hypothesis (its `GetAt`
spec, `HGetAt`, was one too until 7e-1 restated `Client.Get.spec` at any revision).
(`clientErrPlain`, the client's errors are no `APIStatus`, which `errOut`'s
`IsTooLargeResourceVersion` test needs, was one too until 7e-1 made it a lemma,
`clientErrPlain_holds`, from `clientErr`'s `clientErrTys`.)

**Vacuous for now (2026-11-07).** Every `_safe` theorem here, `k8s_etcd3_partition_safe` included,
rests on `pbEnc_ok`, which proves `False` (lean `cffe36ea9d`, `notes/pbenc-ok-inconsistent.md`), and
on grpc's refuted `ProtoMsg` axioms: until etcd-grove-c9's per-type fix lands, they hold vacuously.
They also rest on false axioms until the axiom sweep's repairs of batch 1 land (lean `0eda5f10de`,
`notes/axiom-review/`): `zap.Logger.{Debug,Error,Fatal,Info,Warn}`, `errors.IsCtxErr`,
`context.ValueStartTime` (a theorem since sweep repairs 1's B2, 2026-11-08), `http.Handle_ok`, and
the k8s `DefaultFeatureGate` and `DefaultFeatureSupportChecker` initializers.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Adequacy

@[expose] public section

set_option pp.fullNames true
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [NaInvG GF]

/-- **`Main` does not panic** (`Link.lean`'s `k8s_etcd3.wp_Main`). -/
theorem k8setcd3_Main [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [ContextReadErrs (GF := GF) (hG := hG)]
    (h_Client__List : kubernetes.Client.List.spec (GF := GF) (hG := hG)) :
    k8s_etcd3.Main.spec (GF := GF) (hG := hG) :=
  k8s_etcd3.wp_Main h_Client__List

/-- **`MainCluster` does not panic** (`MainLinked.lean`'s `k8s_etcd3.wp_MainCluster`). -/
theorem k8setcd3_MainCluster [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [ContextReadErrs (GF := GF) (hG := hG)]
    (h_Client__List : kubernetes.Client.List.spec (GF := GF) (hG := hG)) :
    k8s_etcd3.MainCluster.spec (GF := GF) (hG := hG) :=
  k8s_etcd3.wp_MainCluster h_Client__List

/-- **`MainPartition` does not panic** (`MainLinked.lean`'s `k8s_etcd3.wp_MainPartition`). -/
theorem k8setcd3_MainPartition [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [ContextReadErrs (GF := GF) (hG := hG)]
    (h_Client__List : kubernetes.Client.List.spec (GF := GF) (hG := hG)) :
    k8s_etcd3.MainPartition.spec (GF := GF) (hG := hG) :=
  k8s_etcd3.wp_MainPartition h_Client__List

end results

section adequacy
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt
variable [go_gctx : GoGlobalContext]

/-- **The Kubernetes etcd3 store's linearizability instance is safe, in the operational semantics** (`k8s_etcd3_adequate`,
see the file header and `Adequacy.lean`). -/
theorem k8s_etcd3_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8setcd3GF, ContextReadErrs (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (HList : ∀ hG : HeapGS .hasLC k8setcd3GF,
      kubernetes.Client.List.spec (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_putget.BootFacts id ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (clients ops : w64)
    (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (HNs : prometheus.namesUnclaimed (k8setcd3Program clients ops) k8setcd3Names)
    (HAs : addrsUnclaimed (k8setcd3Program clients ops) [go!"127.0.0.1:23896"])
    -- (2026-11-03, the WAL's API, change 6; sweep repairs 1, W3/W4) the member's data directory, fresh at start (`dataDirsAbsent`)
    (HDs : dataDirsAbsent (k8setcd3Program clients ops) [go!"k8setcd3.etcd"])
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    (HEnv : verifyEnvOff (k8setcd3Program clients ops))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC k8setcd3GF,
      ⊢ k8s_etcd3.premises (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([k8setcd3Program clients ops], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  k8s_etcd3_adequate Hctx HList id ctxs boot Hbf Hck Haf Hbuq Hrf Hdbo clients ops Hc0 Hc31 Hops
    Hmul HNs HAs HDs HEnv n Hprem σ g Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn


/-- **The Kubernetes etcd3 store's linearizability instance over three members is safe, in the
operational semantics** (`k8s_etcd3_cluster_adequate`, see the file header and `Adequacy.lean`). -/
theorem k8s_etcd3_cluster_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8setcd3GF, ContextReadErrs (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (HList : ∀ hG : HeapGS .hasLC k8setcd3GF,
      kubernetes.Client.List.spec (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : cluster3.BootFacts id₁ id₂ id₃ ps ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (clients ops : w64)
    (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (HNs : prometheus.namesUnclaimed (k8setcd3CProgram clients ops) k8setcd3Names)
    (HAs : addrsUnclaimed (k8setcd3CProgram clients ops) k8setcd3CAddrs)
    (HDs : dataDirsAbsent (k8setcd3CProgram clients ops) k8setcd3CDataDirs)
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    (HEnv : verifyEnvOff (k8setcd3CProgram clients ops))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC k8setcd3GF,
      ⊢ cluster3.premises (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx) k8s_etcd3.clusterCfg n
        id₁ id₂ id₃ ps ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([k8setcd3CProgram clients ops], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  k8s_etcd3_cluster_adequate Hctx HList id₁ id₂ id₃ ps ctxs boot Hbf Hck Haf Hbuq Hrf Hdbo clients ops
    Hc0 Hc31 Hops Hmul HNs HAs HDs HEnv n Hprem σ g Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

/-- **The Kubernetes etcd3 store's linearizability instance over three members under any partition
schedule is safe, in the operational semantics** (`k8s_etcd3_partition_adequate`, see the file
header and `Adequacy.lean`; vacuous until the `pbEnc_ok` fix lands, and resting on false axioms until the sweep's batch-1 repairs land: see the file header). -/
theorem k8s_etcd3_partition_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8setcd3GF, ContextReadErrs (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (HList : ∀ hG : HeapGS .hasLC k8setcd3GF,
      kubernetes.Client.List.spec (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : cluster3.BootFacts id₁ id₂ id₃ ps ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (clients ops : w64)
    (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps : steps.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (k8setcd3PProgram clients ops steps) k8setcd3Names)
    (HAs : addrsUnclaimed (k8setcd3PProgram clients ops steps) k8setcd3CAddrs)
    (HDs : dataDirsAbsent (k8setcd3PProgram clients ops steps) k8setcd3CDataDirs)
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    (HEnv : verifyEnvOff (k8setcd3PProgram clients ops steps))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC k8setcd3GF,
      ⊢ cluster3.premises (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx) k8s_etcd3.clusterCfg n
        id₁ id₂ id₃ ps ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNsteps n ([k8setcd3PProgram clients ops steps], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  k8s_etcd3_partition_adequate Hctx HList id₁ id₂ id₃ ps ctxs boot Hbf Hck Haf Hbuq Hrf Hdbo clients ops
    Hc0 Hc31 Hops Hmul steps Hsteps HNs HAs HDs HEnv n Hprem σ g Hlctx Hinit Hthreads κs t2 σ2
    Hsteps' Hn

end adequacy

#print axioms k8setcd3_Main
#print axioms k8s_etcd3_adequate
#print axioms k8s_etcd3_safe
#print axioms k8setcd3_MainCluster
#print axioms k8s_etcd3_cluster_adequate
#print axioms k8s_etcd3_cluster_safe
#print axioms k8setcd3_MainPartition
#print axioms k8s_etcd3_partition_adequate
#print axioms k8s_etcd3_partition_safe

end EtcdGrove
end Perennial

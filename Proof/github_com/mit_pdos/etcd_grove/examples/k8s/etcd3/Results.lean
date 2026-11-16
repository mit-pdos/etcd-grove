/-
The Kubernetes etcd3 store's linearizability instance's results
(`examples/k8s/etcd3/k8s_etcd3.go`; stage 6g of `notes/k8s-etcd3-plan.md`), restated, with the
trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`k8setcd3_Main`** (`Link.lean`'s `k8s_etcd3.wp_Main`): `Main(clients, ops)` -- one etcd member
  started in process, a kubernetes client configured for one attempt per call, the seed objects,
  the Kubernetes etcd3 store over the client (`etcd3.New`, the driver's codec, versioner,
  transformer and decoder), `Check(s, st0, clients, ops, 0)` (`lintest.Run` with the driver's Go
  model of the store, `Apply` over the store: `Create`, `Get`, `Delete`, `GuaranteedUpdate`, and
  `GetList` (with selectors and the past-revision modes; stage 7e: the store pages through the
  result itself, but the driver never sends a continue token, so `storage.DecodeContinue` and
  `GetList`'s continue-key branch are not covered);
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
  over cluster3" in `notes/k8s-etcd3-plan.md`, 2026-11-06; `k` members since stage A of
  `notes/k8s-7f6-scope.md`, 2026-11-16, approved by the user): `MainCluster(k, clients, ops)` --
  `Main` over a `k`-member cluster (`startCluster`: the examples' generic start, each member behind a
  bridge, the client of the `k` bridges with etcd's default retries) -- does not panic and returns
  `Ok` or `Unknown`, for every `1 ≤ k ≤ 1000`
  (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/MainCluster.lean`).
* **`k8s_etcd3_cluster_safe`** (`Adequacy.lean`'s `k8s_etcd3_cluster_adequate`): its closed
  theorem, `k8s_etcd3_safe`'s conclusion for `MainCluster(k, clients, ops)`, for every
  `1 ≤ k ≤ 1000`, under the cluster's hypotheses (its boot facts in putgetN's list form and premises
  at its members, its `3k` addresses unclaimed, its `k` data directories fresh) for the one member's.
* **`k8setcd3_MainPartition`** (`MainLinked.lean`'s `k8s_etcd3.wp_MainPartition`; step 2 of "k8s
  etcd3 over cluster3", 2026-11-07; `k` members since stage A): `MainPartition(k, clients, ops,
  sched)` -- `MainCluster` with
  `cluster3.Partitioner` running the schedule (peer cuts and mends, a bridge blackholed or
  unblackholed, its connections dropped) while `Check`'s clients run -- does not panic and returns
  `Ok` or `Unknown`, for every schedule
  (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/MainPartition.lean`).
* **`k8s_etcd3_partition_safe`** (`Adequacy.lean`'s `k8s_etcd3_partition_adequate`): its closed
  theorem, `k8s_etcd3_cluster_safe`'s conclusion for `MainPartition(k, clients, ops, sched)` with the
  schedule `steps` built as a slice literal (`schedLit`), for every `steps` of fewer than `2 ^ 63`
  steps, under `k8s_etcd3_cluster_safe`'s hypotheses.

**No pending hypotheses (k8s 7e-1, 2026-11-10).** The client's `List` spec, `GetAt` spec and
`clientErrPlain` were hypotheses of every result here during 7e-4; 7e-1 proved `Client.List`
(`client/v3/kubernetes/Client__List.lean`), restated `Client.Get.spec` at any revision, and made
`clientErrPlain` a lemma (`clientErrPlain_holds`).

**The refuted axioms these results rested on are repaired (checked 2026-11-12 against
`notes/STATUS.md`).** Axiom sweep batch 1 (2026-11-07) refuted two families the `_safe` theorems
reach; premise fixes 6 (2026-11-11, STATUS "Premise fixes 6") repaired both: `errors.IsCtxErr` takes
`context.isCtxErr err` in place of `isTypedErr err` (`notes/axiom-review/isctxerr.md`), and
`zap.Logger.{Debug,Error,Fatal,Info,Warn}` take `zapLoggerOk l` in place of `l ≠ null` (`Panic`
keeps `l ≠ null`). The batch's other ones were repaired by sweep repairs 1 (`http.Handle`, B3; the
default feature gate's and `DefaultFeatureSupportChecker`'s initializers, B5; `context.ValueStartTime`,
a theorem since B2). The inconsistent `pbEnc_ok` axiom was deleted by per-type stage A (lean
`de9c19e020`, 2026-11-10), and grpc's axioms that took any message model (`ProtoMsg`, `StreamMsg`)
take registered ones since stages A and B (lean `51e51adb99`, 2026-11-12).
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
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [ContextReadErrs (GF := GF) (hG := hG)] :
    k8s_etcd3.Main.spec (GF := GF) (hG := hG) :=
  k8s_etcd3.wp_Main

/-- **`MainCluster` does not panic** (`MainLinked.lean`'s `k8s_etcd3.wp_MainCluster`). -/
theorem k8setcd3_MainCluster [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [ContextReadErrs (GF := GF) (hG := hG)] :
    k8s_etcd3.MainCluster.spec (GF := GF) (hG := hG) :=
  k8s_etcd3.wp_MainCluster

/-- **`MainPartition` does not panic** (`MainLinked.lean`'s `k8s_etcd3.wp_MainPartition`). -/
theorem k8setcd3_MainPartition [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [ContextReadErrs (GF := GF) (hG := hG)] :
    k8s_etcd3.MainPartition.spec (GF := GF) (hG := hG) :=
  k8s_etcd3.wp_MainPartition

end results

section adequacy
attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs
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
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_putget.BootFacts id ctxs boot)
    (Haf : authRecordsFit)
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
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([k8setcd3Program clients ops], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  k8s_etcd3_adequate Hctx id ctxs boot Hbf Haf Hbuq Hrf Hdbo clients ops Hc0 Hc31 Hops
    Hmul HNs HAs HDs HEnv n Hprem σ g Hfs Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn


/-- **The Kubernetes etcd3 store's linearizability instance over `k` members is safe, in the
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
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)
    (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : k8s_etcd3N.BootFacts ids ps ctxs boot)
    (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (clients ops : w64)
    (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (HNs : prometheus.namesUnclaimed (k8setcd3CProgram k clients ops) k8setcd3Names)
    (HAs : addrsUnclaimed (k8setcd3CProgram k clients ops) (k8s_etcd3N.k8setcd3NAddrs k))
    (HDs : dataDirsAbsent (k8setcd3CProgram k clients ops) (k8s_etcd3N.k8setcd3NDirs k))
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    (HEnv : verifyEnvOff (k8setcd3CProgram k clients ops))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC k8setcd3GF,
      ⊢ k8s_etcd3N.premises (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([k8setcd3CProgram k clients ops], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  k8s_etcd3_cluster_adequate Hctx k hk1 hk ids ps ctxs boot Hlen Hbf Haf Hbuq Hrf Hdbo clients ops
    Hc0 Hc31 Hops Hmul HNs HAs HDs HEnv n Hprem σ g Hfs Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

/-- **The Kubernetes etcd3 store's linearizability instance over `k` members under any partition
schedule is safe, in the operational semantics** (`k8s_etcd3_partition_adequate`, see the file
header and `Adequacy.lean`; the `zap.Logger` and `errors.IsCtxErr` axioms it once rested on were
refuted and are repaired since premise fixes 6: see the file header). -/
theorem k8s_etcd3_partition_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8setcd3GF, ContextReadErrs (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)
    (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : k8s_etcd3N.BootFacts ids ps ctxs boot)
    (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (clients ops : w64)
    (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps : steps.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (k8setcd3PProgram k clients ops steps) k8setcd3Names)
    (HAs : addrsUnclaimed (k8setcd3PProgram k clients ops steps) (k8s_etcd3N.k8setcd3NAddrs k))
    (HDs : dataDirsAbsent (k8setcd3PProgram k clients ops steps) (k8s_etcd3N.k8setcd3NDirs k))
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    (HEnv : verifyEnvOff (k8setcd3PProgram k clients ops steps))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC k8setcd3GF,
      ⊢ k8s_etcd3N.premises (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNsteps n ([k8setcd3PProgram k clients ops steps], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  k8s_etcd3_partition_adequate Hctx k hk1 hk ids ps ctxs boot Hlen Hbf Haf Hbuq Hrf Hdbo clients ops
    Hc0 Hc31 Hops Hmul steps Hsteps HNs HAs HDs HEnv n Hprem σ g Hfs Hlctx Hinit Hthreads κs t2 σ2
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

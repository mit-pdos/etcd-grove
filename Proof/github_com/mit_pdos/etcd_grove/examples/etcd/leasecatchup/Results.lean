/-
The multi-member lease example's results (`examples/etcd/leasecatchup/leasecatchup.go`; lease-mono3
step 1, 2026-11-06, `notes/lease-mono3-plan.md`), restated, with the trust base of each printed in
the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`leasecatchup_Main`** (`MainLinked.lean`): `Main` -- three etcd members started in process in
  the monotone lease mode (`cluster3.StartCluster`), a client of member 3's bridge and one of member
  1's, a lease granted through member 3, member 3 cut off while fillers are granted through member 1,
  the links mended, member 3's listing polled until it lists the last filler, and a panic unless it
  lists the first lease too -- returns: it does not panic. From `isPkgInit leasecatchup`, the
  cluster's start bundle, the main thread's token and the cluster's named premises
  (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leasecatchup/Main.lean`).
* **`etcd_leasecatchup_safe`** (`Adequacy.lean`'s `etcd_leasecatchup_adequate`): the closed
  theorem. Every real execution of `n` steps of `leasecatchup`'s initialization followed by
  `Main()`, from a fresh state with one thread, has no stuck thread, no thread ended in a panic, and
  the main thread's result, if any, is `#()`; under the hypotheses of the three-member partition
  examples (`k8s_compactor_partition_safe`'s, without its schedule and `clock.RealClock.After`) and
  leasegrant's lease hypotheses (`leasePeersOk`, `lease.leasesNoExpiry`). It is the first closed
  result over a configuration in which a member's lessor is rebuilt from a snapshot in Go (the
  example's test counts a merged snapshot sent to member 3 and its lease store restored, every run;
  `Adequacy.lean`'s header).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Adequacy

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `etcd_leasecatchup.wp_Main`). -/
theorem leasecatchup_Main [go_etcd_io.etcd.cache.v3.Assumptions] [Float64ToInt64Semantics]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_leasecatchup.Main.spec (GF := GF) (hG := hG) :=
  etcd_leasecatchup.wp_Main

end results

section adequacy
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt
variable [go_gctx : GoGlobalContext]

/-- **The multi-member lease example is safe, in the operational semantics**
(`etcd_leasecatchup_adequate`, see the file header and `Adequacy.lean`). -/
theorem etcd_leasecatchup_safe [lctx : GoLocalContext] [sem : go.Semantics]
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
    (HAs : addrsUnclaimed leasecatchupProgram leasecatchupAddrs)   -- 3 peer, 3 client, 3 bridge
    (HDs : dataDirsAbsent leasecatchupProgram leasecatchupDataDirs)
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    (HEnv : verifyEnvOff leasecatchupProgram)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC leasecatchupGF,
      ⊢ cluster3.premises (GF := leasecatchupGF) (hG := heapAtLcu hG lctx)
          etcd_leasecatchup.clusterCfg n id₁ id₂ id₃ ps ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([leasecatchupProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  etcd_leasecatchup_adequate Hctx Hcec id₁ id₂ id₃ ps ctxs boot Hbf Hck Haf Hbuq Hrf Hdbo Hlp Hlne
    HNs HAs HDs HEnv n Hprem σ g Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

end adequacy

#print axioms leasecatchup_Main
#print axioms etcd_leasecatchup_adequate
#print axioms etcd_leasecatchup_safe

end EtcdGrove
end Perennial

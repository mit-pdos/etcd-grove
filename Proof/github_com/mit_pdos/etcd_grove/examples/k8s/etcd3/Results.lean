/-
The Kubernetes etcd3 store's linearizability instance's results
(`examples/k8s/etcd3/k8s_etcd3.go`; stage 6g of `notes/k8s-etcd3-plan.md`), restated, with the
trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`k8setcd3_Main`** (`Link.lean`'s `k8s_etcd3.wp_Main`): `Main(clients, ops, watchers, wops)` -- one etcd member
  started in process, a kubernetes client configured for one attempt per call, the seed objects,
  the Kubernetes etcd3 store over the client (`etcd3.New`, the driver's codec, versioner,
  transformer and decoder), `Check(s, st0, h0, clients, ops, watchers, wops, 0)` (`lintest.RunLin2` with the driver's Go
  model of the store, `Apply` over the store: `Create`, `Get`, `Delete`, `GuaranteedUpdate`, and
  `GetList` (with selectors and the past-revision modes; stage 7e: the store pages through the
  result itself, but the driver never sends a continue token, so `storage.DecodeContinue` and
  `GetList`'s continue-key branch are not covered);
  since 7f-6 stage E `watchers` watchers of `wops` random watches each through the store's `Watch`,
  checked against the model's watch observation; porcupine's checker), and a panic if porcupine answers `Illegal` -- does not panic and returns
  `Ok` or `Unknown`. From `isPkgInit k8setcd3`, the right to listen on `127.0.0.1:23896`, the main
  thread's token and `Main`'s named premises
  (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/Main.lean`), at the context errors'
  premise `ContextReadErrs` (k8s etcd3 7c-2 part 2, S7: the compactor's channel context's errors'
  descriptions; `k8s_etcd3_safe` already took it, `Hctx`).
* **`k8setcd3_MainCluster`** (`MainLinked.lean`'s `k8s_etcd3.wp_MainCluster`; step 1 of "k8s etcd3
  over cluster3" in `notes/k8s-etcd3-plan.md`, 2026-11-06; `k` members since stage A of
  `notes/k8s-7f6-scope.md`, 2026-11-16, approved by the user): `MainCluster(k, clients, ops, watchers, wops)` --
  `Main` over a `k`-member cluster (`startCluster`: the examples' generic start, each member behind a
  bridge, the client of the `k` bridges with etcd's default retries) -- does not panic and returns
  `Ok` or `Unknown`, for every `1 ≤ k ≤ 1000`
  (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/MainCluster.lean`).
* **`k8setcd3_MainPartition`** (`MainLinked.lean`'s `k8s_etcd3.wp_MainPartition`; step 2 of "k8s
  etcd3 over cluster3", 2026-11-07; `k` members since stage A): `MainPartition(k, clients, ops,
  watchers, wops, sched)` -- `MainCluster` with
  `cluster3.Partitioner` running the schedule (peer cuts and mends, a bridge blackholed or
  unblackholed, its connections dropped) while `Check`'s clients run -- does not panic and returns
  `Ok` or `Unknown`, for every schedule
  (`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/MainPartition.lean`).

**The closed theorems retired (2026-11-20, the user's decision D3 of `notes/k8s-unified-scope.md`).**
Its closed theorems `k8s_etcd3_safe`, `k8s_etcd3_cluster_safe` and `k8s_etcd3_partition_safe`
(with `Adequacy.lean`, `TopLevelDefs.lean` and the `TopLevelRobustness.lean` pair) are gone: the one closed Kubernetes theorem `k8s_safe` (`examples/k8s/all`,
`Proof/github_com/mit_pdos/etcd_grove/examples/k8s/all/Results.lean`) runs `MainPartition` beside the
compactor driver's in one process; the function triples here stay (`k8setcd3_MainPartition` is its callee).

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

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainLinked

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
theorem k8setcd3_Main [_root_.Perennial.net.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [ContextReadErrs (GF := GF) (hG := hG)] :
    k8s_etcd3.Main.spec (GF := GF) (hG := hG) :=
  k8s_etcd3.wp_Main

/-- **`MainCluster` does not panic** (`MainLinked.lean`'s `k8s_etcd3.wp_MainCluster`). -/
theorem k8setcd3_MainCluster [_root_.Perennial.net.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [ContextReadErrs (GF := GF) (hG := hG)] :
    k8s_etcd3.MainCluster.spec (GF := GF) (hG := hG) :=
  k8s_etcd3.wp_MainCluster

/-- **`MainPartition` does not panic** (`MainLinked.lean`'s `k8s_etcd3.wp_MainPartition`). -/
theorem k8setcd3_MainPartition [_root_.Perennial.net.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [ContextReadErrs (GF := GF) (hG := hG)] :
    k8s_etcd3.MainPartition.spec (GF := GF) (hG := hG) :=
  k8s_etcd3.wp_MainPartition

end results

#print axioms k8setcd3_Main
#print axioms k8setcd3_MainCluster
#print axioms k8setcd3_MainPartition

end EtcdGrove
end Perennial

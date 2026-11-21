/-
txnlinfaultsN's results (`examples/etcd/txnlinfaultsN/txnlinfaultsN.go`; `notes/txnlinfaultsN-plan.md`,
2026-11-15), restated, with the trust base of each printed in the build log (`#print axioms`). Lean-first
(no Rocq counterpart).

* **`txnlinfaultsN_Main`** (`MainLinked.lean`): `Main(k, clients, ops, sched)` -- `k` etcd members started in
  process with the generic start (`etcdstart.Members`, `etcdstart.StartMembers`, partition's snapshot
  settings `SnapCount = SnapCatchUp = 1`), each member's gRPC server on its client address
  (`127.0.0.1:27000+i`) behind a copy of etcd's test bridge (`127.0.0.1:28000+i`), `k` clients each of all
  `k` bridges (failover, D27), the partitioner forked on the schedule (`cluster3.Partitioner`: the links
  between members cut and mended with etcd's own `CutPeer`/`MendPeer`, both directions; each member's
  bridge blackholed, unblackholed or its connections dropped; a step naming a member index `≥ k` does
  nothing), partition's `Check` (txnlin's workload: gets, ranges, puts, deletes and transactions, each
  through a client picked at random, checked by porcupine against txnlin's model), and a panic if
  porcupine answers `Illegal` -- does not panic and returns `Ok` or `Unknown`, **for every schedule** and
  every member count `1 ≤ k ≤ 1000` (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/txnlinfaultsN/Main.lean`).
* **`etcd_txnlinfaultsN_safe`** (`Adequacy.lean`'s `etcd_txnlinfaultsN_adequate`): the closed theorem,
  `etcd_partition_safe` for every member count `1 ≤ k ≤ 1000` (no parity premise, as putgetN's), with
  partition's premises and putgetN's generalization of the three members to a list; no new premise. Its
  statement was approved by the user, 2026-11-15, via etcd-grove-81 (`notes/txnlinfaultsN-draft.md`).

**The cluster token.** The program's token is `txnlinfaultsN-12748`, which appears only in the program and its
premises (the members' configurations in `etcd_txnlinfaultsN.premises`). etcd computes each member's id
from its peer URL and the token, and `BootFacts` (putgetN's) requires the ids' 16 low bits distinct and not
`0` (etcd's request and lease ids carry them as the member's prefix). For a token chosen at random that
fails for some `k ≤ 1000` (the birthday bound of 16 bits), which would make the theorem vacuous at those `k`;
putgetN's token does not carry over, since the peer URLs differ. `txnlinfaultsN-12748` is the first
`txnlinfaultsN-<i>` at which the premise holds for every `k ≤ 1000` (member `i`'s id is the same in every
cluster of more than `i` members, so the check at `k = 1000` covers every `k`) and across the clusters of
`examples/etcd/all` (the others at `k ≤ 300`; until 2026-11-21 `txnlinfaultsN-6255`); `TestMemberIDs`
(`examples/etcd/txnlinfaultsN/txnlinfaultsN_test.go`) checks it for every `k`, from the ids etcd computes,
without starting a cluster.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Adequacy
public import Robustness.Statement

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Assumptions]
variable [NaInvG GF]

/-- **`Main(k, clients, ops, sched)` does not panic, for every schedule** (`MainLinked.lean`'s
`etcd_txnlinfaultsN.wp_Main`). -/
theorem txnlinfaultsN_Main [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_txnlinfaultsN.Main.spec (GF := GF) (hG := hG) :=
  etcd_txnlinfaultsN.wp_Main

end results

section adequacy
attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr
variable [go_gctx : GoGlobalContext]

/-- **txnlinfaultsN is safe, in the operational semantics, for every member count `1 ≤ k ≤ 1000` and every
schedule** (`etcd_txnlinfaultsN_adequate`, see the file header and `Adequacy.lean`). -/
theorem etcd_txnlinfaultsN_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC linkvGF, ContextReadErrs (GF := linkvGF) (hG := linkvHeapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC linkvGF, ContextErrsClient (GF := linkvGF) (hG := linkvHeapAt hG lctx))
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)
    (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : etcd_txnlinfaultsN.BootFacts ids ps ctxs boot)
    (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (clients ops : w64)
    (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (steps : List github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Step)
    (Hsteps : steps.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (txnlinfaultsNProgram k clients ops steps) txnlinfaultsNNames)
    (HAs : addrsUnclaimed (txnlinfaultsNProgram k clients ops steps)
      (etcd_txnlinfaultsN.txnlinfaultsNAddrs k))
    (HDs : dataDirsAbsent (txnlinfaultsNProgram k clients ops steps)
      (etcd_txnlinfaultsN.txnlinfaultsNDirs k))
    (HEnv : verifyEnvOff (txnlinfaultsNProgram k clients ops steps))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC linkvGF,
      ⊢ etcd_txnlinfaultsN.premises (GF := linkvGF) (hG := linkvHeapAt hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (etcd_txnlinfaultsN.txnlinfaultsNDirs k))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNstepsBelow (2 ^ 28) n ([txnlinfaultsNProgram k clients ops steps], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 12 ≤ 2 ^ 40) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  etcd_txnlinfaultsN_adequate Hctx Hcec k hk1 hk ids ps ctxs boot Hlen Hbf Haf Hbuq Hrf Hdbo clients ops
    Hc0 Hc31 Hops Hmul steps Hsteps HNs HAs HDs HEnv n Hprem σ g Hfs HWal Hlctx Hinit Hthreads κs t2 σ2 Hsteps' Hn

end adequacy

#print axioms txnlinfaultsN_Main
#print axioms etcd_txnlinfaultsN_adequate
#print axioms etcd_txnlinfaultsN_safe

end EtcdGrove
end Perennial

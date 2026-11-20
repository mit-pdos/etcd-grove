/-
leaseN's results (`examples/etcd/leaseN/leaseN.go`; `notes/leaseN-plan.md`, 2026-11-16), restated, with the
trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`leaseN_Main`** (`MainLinked.lean`): `Main(k)` -- `k` etcd members started in process
  (`etcdstart.Members`, `etcdstart.StartMembers`), every member's gRPC server listening at its client
  address `127.0.0.1:(11000+i)`, and at every member, through a client of that member, `Leases()` and
  `TimeToLive(7)`, with a panic if the listing has a lease twice or the answer is about another lease
  -- returns: it does not panic (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseN/Main.lean`),
  for `1 ≤ k ≤ 1000`.
* **`etcd_leaseN_safe`** (`Adequacy.lean`'s `etcd_leaseN_adequate`): the closed theorem, `etcd_lease_safe`
  for every member count `1 ≤ k ≤ 1000`. Its statement was approved by the user, 2026-11-16, via
  etcd-grove-02 (`notes/leaseN-plan.md` §2.1).

**The cluster token.** `leaseN-2422`, the first `leaseN-<i>` at which putgetN's `BootFacts` (the ids' 16 low
bits distinct and not `0`) holds for every `k ≤ 1000`; `TestMemberIDs` (`examples/etcd/leaseN/leaseN_test.go`)
checks it from the ids etcd computes. No member grants a lease, so the ids' 15 low bits need not be distinct.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Adequacy
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Assumptions]

/-- **`Main(k)` does not panic** (`MainLinked.lean`'s `etcd_leaseN.wp_Main`). -/
theorem leaseN_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_leaseN.Main.spec (GF := GF) (hG := hG) :=
  etcd_leaseN.wp_Main

end results

section adequacy
attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr
variable [go_gctx : GoGlobalContext]

/-- **leaseN is safe, in the operational semantics, for every member count `1 ≤ k ≤ 1000`**
(`etcd_leaseN_adequate`, see the file header and `Adequacy.lean`). -/
theorem etcd_leaseN_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putgetNGF, ContextReadErrs (GF := putgetNGF) (hG := heapAtN hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetNGF, ContextErrsClient (GF := putgetNGF) (hG := heapAtN hG lctx))
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)
    (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : etcd_putgetN.BootFacts ids ps ctxs boot)
    (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (Hlp : leasePeersOk)
    (HNs : prometheus.namesUnclaimed (leaseNProgram k) leaseNNames)
    (HAs : addrsUnclaimed (leaseNProgram k) (etcd_leaseN.leaseNAddrs k))
    (HDs : dataDirsAbsent (leaseNProgram k) (etcd_leaseN.leaseNDirs k))
    (HEnv : verifyEnvOff (leaseNProgram k))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putgetNGF,
      ⊢ etcd_leaseN.premises (GF := putgetNGF) (hG := heapAtN hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (etcd_leaseN.leaseNDirs k))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow (2 ^ 28) n ([leaseNProgram k], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 12 ≤ 2 ^ 40) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  etcd_leaseN_adequate Hctx Hcec k hk1 hk ids ps ctxs boot Hlen Hbf Haf Hbuq Hrf Hdbo Hlp HNs HAs HDs
    HEnv n Hprem σ g Hfs HWal Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

end adequacy

#print axioms leaseN_Main
#print axioms etcd_leaseN_adequate
#print axioms etcd_leaseN_safe

end EtcdGrove
end Perennial

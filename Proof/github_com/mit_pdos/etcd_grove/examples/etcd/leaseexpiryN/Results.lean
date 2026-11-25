/-
leaseexpiryN's results (`examples/etcd/leaseexpiryN/leaseexpiryN.go`; `notes/leaseN-plan.md`, 2026-11-16),
restated, with the trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq
counterpart).

* **`leaseexpiryN_Main`** (`MainLinked.lean`): `Main(k)` -- `k` etcd members started in process
  (`etcdstart.Members`, `etcdstart.StartMembers`), every member's gRPC server listening at its client
  address `127.0.0.1:(13000+i)`, a lease of the minimum TTL granted through a client of every member,
  and at every member, once its listing no longer lists the lease granted through it, one more
  listing, with a panic if it lists the lease -- returns: it does not panic
  (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/leaseexpiryN/Main.lean`), for every `uint64` `k`
  (outside `[1, 1000]` it returns at once).
* **`etcd_leaseexpiryN_safe_single_process`** (`Adequacy.lean`'s `etcd_leaseexpiryN_adequate`): the closed theorem,
  "an expired lease is no longer listed" at every member of a cluster of `1 ≤ k ≤ 1000` members, with no
  premise about time; since 2026-11-24 (P6 of the pure-premises plan) for every `uint64` `k`, `Main`
  checking the range itself. Its statement was approved by the user, 2026-11-16, via etcd-grove-02
  (`notes/leaseN-plan.md` §2.2).

**The cluster token.** `leaseexpiryN-1973196`, the first `leaseexpiryN-<i>` at which putgetN's `BootFacts` (the
ids' 16 low bits distinct and not `0`) and `leaseIdsApart` (their 15 low bits distinct: a lease id carries only
15 bits of its member's id, `issues/etcd-lease-id-mask-member-prefix.md`) hold for every `k ≤ 1000`;
`TestMemberIDs` (`examples/etcd/leaseexpiryN/leaseexpiryN_test.go`) checks both from the ids etcd computes.

(2026-11-23, etcd-grove#28, `notes/single-process-restore.md`: retired at the net swap, tag
`single-process-final`, and restored over the net extension, `etcdNetExts`, under the `_single_process`
name; against the tag the statement gains the instance argument `[net.FieldAssumptions]` and the
network's initial state `Hg : extsInitGlobal g`, the semantics the net extension.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Adequacy
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Assumptions]

/-- **`Main(k)` does not panic** (`MainLinked.lean`'s `etcd_leaseexpiryN.wp_Main`). -/
theorem leaseexpiryN_Main [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_leaseexpiryN.Main.spec (GF := GF) (hG := hG) :=
  etcd_leaseexpiryN.wp_Main

end results

section adequacy
attribute [local instance] etcdNetExts etcdNetExtsSemantics etcdNetExtsInterp etcdNetExts_hasIdIssue
  etcdNetExts_hasFs etcdNetExts_hasNet etcdFsSem etcdFsSemOk etcdFsNoErr
variable [go_gctx : GoGlobalContext]

/-- **leaseexpiryN is safe, in the operational semantics, for every `k`** (`Main(k)` returns at once
outside `[1, 1000]`)
(`etcd_leaseexpiryN_adequate`, see the file header and `Adequacy.lean`). -/
theorem etcd_leaseexpiryN_safe_single_process [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseexpiryN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel] [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions]
    (Hctx : ∀ hG : HeapGS .hasLC putgetNGF, ContextReadErrs (GF := putgetNGF) (hG := heapAtN hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetNGF, ContextErrsClient (GF := putgetNGF) (hG := heapAtN hG lctx))
    (k : w64)
    (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = uint.nat k) (Hbf : etcd_putgetN.BootFacts ids ps ctxs boot)
    (Hap : leaseIdsApart ids)
    (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (Hlp : leasePeersOk)
    (HAs : addrsUnclaimed (leaseexpiryNProgram k) (etcd_leaseexpiryN.leaseexpiryNAddrs k))
    (HDs : dataDirsAbsent (leaseexpiryNProgram k) (etcd_leaseexpiryN.leaseexpiryNDirs k))
    (HEnv : EtcdVerifyOff)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putgetNGF,
      ⊢ etcd_leaseexpiryN.premises (GF := putgetNGF) (hG := heapAtN hG lctx) (uint.nat k) n ids ps
        ctxs boot)
    (σ : state) (g : GlobalState) (Hg : extsInitGlobal g)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    -- (wal-link P2) the members' WAL areas exist at start and hold no WAL
    (HWal : etcdWalAreasInit (extLocal Fs.fsExt σ.world) (etcd_leaseexpiryN.leaseexpiryNDirs k))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow (2 ^ 28) n ([leaseexpiryNProgram k], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 1 ≤ 2 ^ 48) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  etcd_leaseexpiryN_adequate Hctx Hcec k ids ps ctxs boot Hlen Hbf Hap Haf Hbuq Hrf Hdbo Hlp HAs HDs
    HEnv n Hprem σ g Hg Hfs HWal Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

end adequacy

#print axioms leaseexpiryN_Main
#print axioms etcd_leaseexpiryN_adequate
#print axioms etcd_leaseexpiryN_safe_single_process

end EtcdGrove
end Perennial

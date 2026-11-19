/-
putgetN's results (`examples/etcd/putgetN/putgetN.go`; the clusterN Scope, `notes/clusterN-scope.md`,
2026-11-15), restated, with the trust base of each printed in the build log (`#print axioms`).
Lean-first (no Rocq counterpart).

* **`putgetN_Main`** (`MainLinked.lean`): `Main(k)` -- `k` etcd members started in process
  (`etcdstart.Members`, `etcdstart.StartMembers`: `NewServer`, the raft handler served on the member's
  peer listener, `Start`), member `0`'s gRPC server listening at `127.0.0.1:25000`, a client, a `Put`
  of `k` with value `v`, a `Get` of `k`, and a panic unless the `Get` returned `v` -- returns: it does
  not panic (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/putgetN/Main.lean`), for `1 ≤ k ≤ 1000`.
* **`etcd_putgetN_safe`** (`Adequacy.lean`'s `etcd_putgetN_adequate`): the closed theorem, putget3's for
  every member count `1 ≤ k ≤ 1000` (no parity premise: an even cluster is as safe, only less fault
  tolerant). Its statement was approved by the user, 2026-11-15, via etcd-grove-81
  (`notes/putgetN-draft.md`).

**The cluster token.** The program's token is `putgetN-1405`, which appears only in the program and its
premises (the members' configurations in `etcd_putgetN.premises`). etcd computes each member's id from its
peer URL and the token, and `BootFacts` (as putget3's) requires the ids' 16 low bits distinct and not `0`
(etcd's request and lease ids carry them as the member's prefix). For a token chosen at random that fails
for some `k ≤ 1000` (the birthday bound of 16 bits: at the token `putgetN` first at `k = 214`), which would
make the theorem vacuous at those `k`. `putgetN-1405` is the first `putgetN-<i>` at which the premise holds
for every `k ≤ 1000`; `TestMemberIDs` (`examples/etcd/putgetN/putgetN_test.go`) checks it for every `k`,
from the ids etcd computes, without starting a cluster.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Adequacy
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Assumptions]

/-- **`Main(k)` does not panic** (`MainLinked.lean`'s `etcd_putgetN.wp_Main`). -/
theorem putgetN_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_putgetN.Main.spec (GF := GF) (hG := hG) :=
  etcd_putgetN.wp_Main

end results

section adequacy
attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr
variable [go_gctx : GoGlobalContext]

/-- **putgetN is safe, in the operational semantics, for every member count `1 ≤ k ≤ 1000`**
(`etcd_putgetN_adequate`, see the file header and `Adequacy.lean`). -/
theorem etcd_putgetN_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.putgetN.Assumptions]
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
    (HNs : prometheus.namesUnclaimed (putgetNProgram k) putgetNNames)
    (HAs : addrsUnclaimed (putgetNProgram k) (etcd_putgetN.putgetNAddrs k))
    (HDs : dataDirsAbsent (putgetNProgram k) (etcd_putgetN.putgetNDirs k))
    (HEnv : verifyEnvOff (putgetNProgram k))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putgetNGF,
      ⊢ etcd_putgetN.premises (GF := putgetNGF) (hG := heapAtN hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([putgetNProgram k], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  etcd_putgetN_adequate Hctx Hcec k hk1 hk ids ps ctxs boot Hlen Hbf Haf Hbuq Hrf Hdbo HNs HAs HDs
    HEnv n Hprem σ g Hfs Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

end adequacy

#print axioms putgetN_Main
#print axioms etcd_putgetN_adequate
#print axioms etcd_putgetN_safe

end EtcdGrove
end Perennial

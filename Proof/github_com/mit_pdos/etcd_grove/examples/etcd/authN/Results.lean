/-
authN's results (`examples/etcd/authN/authN.go`; `notes/authN-plan.md`, 2026-11-15), restated, with the
trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`authN_Main`** (`MainLinked.lean`'s `etcd_authN.wp_Main`): `Main(k)` -- `k` members with the simple
  token provider, then authkv's run across them (`run`) -- does not panic and returns `Ok`, `Failed` or
  `WatchEnded` (`Spec/.../authN/Main.lean`), for `1 ≤ k ≤ 1000`.
* **`etcd_authN_safe`** (`Adequacy.lean`'s `etcd_authN_adequate`): the closed theorem, auth3's for every
  member count `1 ≤ k ≤ 1000`. Its statement, with the principals at members `0`, `1 mod k` and `2 mod k`,
  was approved by the user, 2026-11-16, via etcd-grove-81 (`notes/authN-draft.md`).

**The cluster token.** The program's token is `authN-1286`, which appears only in the program and its premises
(the members' configurations in `etcd_authN.premises`): the first `authN-<i>` at which putgetN's `BootFacts`
premise (the member ids' 16 low bits distinct and not `0`) holds for every `k ≤ 1000`; `TestMemberIDs`
(`examples/etcd/authN/authN_test.go`) checks it for every `k`, from the ids etcd computes, without starting a
cluster.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.MainLinked
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authN.Assumptions]

/-- **`Main(k)` does not panic** (`MainLinked.lean`'s `etcd_authN.wp_Main`). -/
theorem authN_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_authN.Main.spec (GF := GF) (hG := hG) :=
  etcd_authN.wp_Main

end results

section adequacy
attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs etcdFsSem etcdFsSemOk etcdFsNoErr
variable [go_gctx : GoGlobalContext]

/-- **The authentication example is safe, in the operational semantics, for every member count
`1 ≤ k ≤ 1000`** (`etcd_authN_adequate`, see `Adequacy.lean`'s header for the program and the
hypotheses): every real execution of `n` steps of `authN`'s initialization followed by `Main(k)`, from a
fresh state with one thread, has no stuck thread, no thread ended in a panic, and the main thread's
result, if any, is `0`, `1` or `2`. Not panicking means none of authkv's checks failed, at any member a
principal uses: every member serves gRPC; the auth state is set up and auth enabled through member `0`;
root then makes a linearizable read at every member (the barrier: each member has applied the set-up
before any principal uses it); then the four principals' workloads run at once, each through its member
(the client with no token through member `0`, `u` and the client with a token no provider issued through
member `1 mod k`, `v` through member `2 mod k`; at `k = 3`, auth3's assignment), so each such member
refuses every forbidden request of the principals that use it (writes, ranges, transactions, watches; a
refusal is an error, a watch outside `[a, b)` reports no event) and replies only with keys the principal
may read; root's history watch through member `0` holds only permitted writes, and `u`'s watch through
member `1 mod k` only keys of `[a, b)`.

**What the result does not say:** everything `etcd_auth3_safe`'s list says (liveness; `Failed` and
`WatchEnded` skip the checks after them; a refusal is any error; password checking is not verified; only
the simple token provider; the barrier is the driver's; no snapshot is taken; a token is used only at the
member that issued it; no member fails, restarts or is partitioned), and:
* members `3..k-1` serve and pass the barrier, but no principal uses them: their refusals are not
  exercised;
* for `k ≤ 2` principals share members (at `k = 1` every principal uses member `0`; at `k = 2` `v` uses
  member `0` with the client with no token), so fewer members are checked than at `k ≥ 3`. -/
theorem etcd_authN_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authN.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF, ContextReadErrs (GF := putgetGF) (hG := heapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetGF, ContextErrsClient (GF := putgetGF) (hG := heapAt hG lctx))
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)
    (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : etcd_putgetN.BootFacts ids ps ctxs boot)
    (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed (authNProgram k) authNNames)
    (HAs : addrsUnclaimed (authNProgram k) (etcd_authN.authNAddrs k))
    (HDs : dataDirsAbsent (authNProgram k) (etcd_authN.authNDirs k))
    (HEnv : verifyEnvOff (authNProgram k))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ etcd_authN.premises (GF := putgetGF) (hG := heapAt hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([authNProgram k], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(W64 0) ∨ v = #(W64 1) ∨ v = #(W64 2)) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  etcd_authN_adequate Hctx Hcec k hk1 hk ids ps ctxs boot Hlen Hbf Haf Hbuq Hrf Hdbo HNs HAs HDs
    HEnv n Hprem σ g Hfs Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

end adequacy

#print axioms authN_Main
#print axioms etcd_authN_adequate
#print axioms etcd_authN_safe

end EtcdGrove
end Perennial

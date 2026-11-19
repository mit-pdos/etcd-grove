/-
authlease's results (`examples/etcd/authlease/authlease.go`; auth-lease S4, `notes/auth-lease-s4-draft.md`,
2026-11-19), restated, with the trust base of each printed in the build log (`#print axioms`). Lean-first (no
Rocq counterpart).

* **`authlease_Main`** (`MainLinked.lean`'s `etcd_authlease.wp_Main`): `Main(k)` -- `k` members with the simple
  token provider in the revocable lease mode, then the lease checks across them (`run`) -- does not panic and
  returns `Ok` or `Failed` (`Spec/.../authlease/Main.lean`), for `1 ≤ k ≤ 1000`.
* **`etcd_authlease_safe`** (`Adequacy.lean`'s `etcd_authlease_adequate`): the closed theorem (Draft §2).

**The cluster token.** The program's token is `authlease-3354335`, which appears only in the program and its
premises: the first `authlease-<i>` at which putgetN's `BootFacts` premise and `leaseIdsApart` (the member ids'
15 low bits distinct) hold for every `k ≤ 1000`; `TestMemberIDs` (`examples/etcd/authlease/authlease_test.go`)
checks it for every `k`, from the ids etcd computes, without starting a cluster.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.MainLinked

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]

/-- **`Main(k)` does not panic** (`MainLinked.lean`'s `etcd_authlease.wp_Main`), at D22's named
hypothesis. -/
theorem authlease_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    (hD22 : ⊢ authSchemaSrv (GF := GF)) :
    etcd_authlease.Main.spec (GF := GF) (hG := hG) :=
  etcd_authlease.wp_Main hD22

end results

section adequacy
attribute [local instance] etcdFsExts etcdFsExtsSemantics etcdFsExtsInterp etcdFsExts_hasIdIssue
  etcdFsExts_hasFs
variable [go_gctx : GoGlobalContext]

/-- **The lease example with auth on is safe, in the operational semantics, for every member count
`1 ≤ k ≤ 1000`** (`etcd_authlease_adequate`, see `Adequacy.lean`'s header for the program and the hypotheses):
every real execution of `n` steps of `authlease`'s initialization followed by `Main(k)`, from a fresh state with
one thread, has no stuck thread, no thread ended in a panic, and the main thread's result, if any, is `0` or `1`.
Not panicking means: after the set-up and the lease set-up, with every member past both, every member a principal
uses refused the client with no token and the client with an invalid token every lease method; refused `u` a
leased put (top level and in a transaction) with root's lease `Lz`, the revocation of `Lz`, and `TimeToLive` with
keys and the listing while `Lz` holds a key `u` may not read; refused `v` the same against `u`'s lease; root
afterwards found `z/lease` attached to `Lz` and no `a/x`; and once `u`'s own revocation of `Lu` succeeded, root
found the keys `Lu` held deleted.

**What the result does not say** (Draft §2): liveness (a permitted call may fail: `Failed`); `Failed` skips the
checks after it; a refusal is any error; `KeepAlive` is not checked; the members `3..k-1` serve and pass the
barriers but no principal uses them, and at `k ≤ 2` principals share members; with the examples' peers a permitted
`TimeToLive` or `KeepAlive` at a follower reports a live lease absent (not exercised); the lessor-side checks
(`TimeToLive`, `Leases`) are judged against the receiving member's lessor; the keys `TimeToLive` returns are not
claimed; no snapshot, restart, failure or partition; a token is used only at the member that issued it; the simple
token provider only. -/
theorem etcd_authlease_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.authlease.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF, ContextReadErrs (GF := putgetGF) (hG := heapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetGF, ContextErrsClient (GF := putgetGF) (hG := heapAt hG lctx))
    -- (D22) the auth store's backend with auth on: trusted text, a named hypothesis
    (hD22 : ∀ hG : HeapGS .hasLC putgetGF, ⊢ authSchemaSrv (GF := putgetGF) (hG := heapAt hG lctx))
    (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 1000)
    (ids : List w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hlen : ids.length = k) (Hbf : etcd_putgetN.BootFacts ids ps ctxs boot)
    -- the members' ids distinct in their 15 low bits (`TestMemberIDs`)
    (Hap : leaseIdsApart ids)
    (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    -- peers answer `/leases/internal` as etcd's handler does or not with 200; no lease expires in the run
    (Hlp : leasePeersOk) (Hlne : lease.leasesNoExpiry)
    (HNs : prometheus.namesUnclaimed (authleaseProgram k) authleaseNames)
    (HAs : addrsUnclaimed (authleaseProgram k) (etcd_authlease.authleaseAddrs k))
    (HDs : dataDirsAbsent (authleaseProgram k) (etcd_authlease.authleaseDirs k))
    (HEnv : verifyEnvOff (authleaseProgram k))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ etcd_authlease.premises (GF := putgetGF) (hG := heapAt hG lctx) k n ids ps ctxs boot)
    (σ : state) (g : GlobalState)
    (Hfs : Fs.FsInit (extLocal Fs.fsExt σ.world))
    (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([authleaseProgram k], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(W64 0) ∨ v = #(W64 1)) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  etcd_authlease_adequate Hctx Hcec hD22 k hk1 hk ids ps ctxs boot Hlen Hbf Hap Haf Hbuq Hrf Hdbo Hlp Hlne
    HNs HAs HDs HEnv n Hprem σ g Hfs Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

end adequacy

#print axioms authlease_Main
#print axioms etcd_authlease_adequate
#print axioms etcd_authlease_safe

end EtcdGrove
end Perennial

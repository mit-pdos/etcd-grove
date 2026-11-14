/-
auth3's results (`examples/etcd/auth3/auth3.go`; the auth3 Scope's A1, `notes/auth3-scope.md`),
restated, with the trust base of each printed in the build log (`#print axioms`). Lean-first (no
Rocq counterpart).

* **`auth3_Main`** (`MainLinked.lean`'s `etcd_auth3.wp_Main`): `Main()` -- three members with the
  simple token provider, then authkv's run on the first -- does not panic and returns `Ok`,
  `Failed` or `WatchEnded` (`Spec/.../auth3/Main.lean`).
* **`etcd_auth3_safe`** (`Adequacy.lean`'s `etcd_auth3_adequate`): the closed theorem.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Adequacy
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth3.MainLinked

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `etcd_auth3.wp_Main`), at D22's named
hypothesis. -/
theorem auth3_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [EtcdGrove.ErrorStringLeaf]
    (hD22 : ⊢ authSchemaSrv (GF := GF)) :
    etcd_auth3.Main.spec (GF := GF) (hG := hG) :=
  etcd_auth3.wp_Main hD22

end results

section adequacy
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt
variable [go_gctx : GoGlobalContext]

/-- **The three-member authentication example is safe, in the operational semantics**
(`etcd_auth3_adequate`, see `Adequacy.lean`'s header for the program and the hypotheses): every
real execution of `n` steps of `auth3`'s initialization followed by `Main()`, from a fresh state
with one thread, has no stuck thread, no thread ended in a panic (so none of authkv's checks
failed, on the first member of a three-member cluster whose other members apply every entry,
the auth set-up's and the `Authenticate` entries included, with auth on), and the main thread's
result, if any, is `0`, `1` or `2`.

**What the result does not say:** everything `etcd_auth_safe`'s list says (liveness; `Failed` and
`WatchEnded` skip the history's or `u`'s watch check; a refusal is any error; the cases not
exercised; `u`'s permitted requests need not succeed; password checking is not verified; only the
simple token provider; no client-certificate authentication; a refused watch is read for 2 s
only; the history's check attributes a write to the principal its key names), and:
* every client is a client of the first member, the only one serving gRPC: the other two members
  serve no request, so that a follower enforces the auth state on reads, watches and writes it
  receives is not shown (variant A2's); a follower's application of the set-up's admin entries and
  of the `Authenticate` entries with auth on is exercised, and the history's check covers every
  write the cluster applied;
* no snapshot is sent or installed (the members' `NoSnapCount`/`NoSnapCatchUp`), so the auth
  state is never carried by a snapshot (variant B's);
* tokens are used only at the member that issued them (the client of one endpoint never fails
  over), so a token's validity at another member is not exercised;
* no member fails, restarts or is partitioned. -/
theorem etcd_auth3_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth3.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF, ContextReadErrs (GF := putgetGF) (hG := heapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetGF, ContextErrsClient (GF := putgetGF) (hG := heapAt hG lctx))
    -- (D22) the auth store's backend with auth on: trusted text, a named hypothesis
    (hD22 : ∀ hG : HeapGS .hasLC putgetGF, ⊢ authSchemaSrv (GF := putgetGF) (hG := heapAt hG lctx))
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_putget3.BootFacts id₁ id₂ id₃ ps ctxs boot)
    (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed auth3Program auth3Names)
    (HAs : addrsUnclaimed auth3Program auth3Addrs)
    (HDs : dataDirsAbsent auth3Program [(etcd_auth3.name₁ ++ go!".etcd"), (etcd_auth3.name₂ ++ go!".etcd"), (etcd_auth3.name₃ ++ go!".etcd")])
    (HEnv : verifyEnvOff auth3Program)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ etcd_auth3.premises (GF := putgetGF) (hG := heapAt hG lctx) n id₁ id₂ id₃ ps ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([auth3Program], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(W64 0) ∨ v = #(W64 1) ∨ v = #(W64 2)) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  etcd_auth3_adequate Hctx Hcec hD22 id₁ id₂ id₃ ps ctxs boot Hbf Haf Hbuq Hrf Hdbo HNs HAs HDs
    HEnv n Hprem σ g Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

end adequacy

#print axioms auth3_Main
#print axioms etcd_auth3_adequate
#print axioms etcd_auth3_safe

end EtcdGrove
end Perennial

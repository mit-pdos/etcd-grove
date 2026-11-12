/-
The cache watch example's results (`examples/etcd/cache/etcd_cache.go`), restated, with the trust base
of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`cachekv_Main`** (`Link.lean`'s `etcd_cache.wp_Main`): `Main(nw, nops)` -- the Puts picked, one
  etcd member started in process (since 2026-11-02 with the auto-compactor on, periodic mode
  at 10ms: a compaction of the cache's watch makes the cache re-list), a client with etcd's default configuration, a cache of the prefix over it, the cache's
  watch of the prefix from revision `2`, `nw` writers, the watch read up to the highest successful
  revision, a progress notification of the watch and a check that panics if it is past the last
  event, a check that panics unless the watched events are exactly the writes, then the cache's
  `Get` of the prefix at that revision and a check that panics unless it answers each key's last
  watched value (`checkGet`) -- does not panic and returns `Ok`, `Failed`, `WatchEnded` or
  `GetFailed`. From `isPkgInit cachekv`, the right to listen
  on `127.0.0.1:23873`, the main thread's token and `Main`'s named premises
  (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/cache/Main.lean`).
* **`etcd_cache_safe`** (`Adequacy.lean`'s `etcd_cache_adequate`): the closed theorem. Every real execution
  of `n` steps of `cachekv`'s initialization followed by `Main(nw, nops)`, from a fresh state with
  one thread, has no stuck thread, no thread ended in a panic (so the check never failed), and the
  main thread's result, if any, is `0`, `1`, `2` or `3`; under `watch_safe`'s hypotheses at cachekv's
  configuration.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.cache.Adequacy

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.cache.Assumptions]

/-- **`Main` does not panic** (`Link.lean`'s `etcd_cache.wp_Main`). -/
theorem cachekv_Main [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_cache.Main.spec (GF := GF) (hG := hG) :=
  etcd_cache.wp_Main

end results

section adequacy
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt
variable [go_gctx : GoGlobalContext]

/-- **The cache watch example is safe, in the operational semantics** (`etcd_cache_adequate`, see the file
header and `Adequacy.lean`). -/
theorem etcd_cache_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.cache.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF, ContextReadErrs (GF := putgetGF) (hG := heapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetGF, ContextErrsClient (GF := putgetGF) (hG := heapAt hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_putget.BootFacts id ctxs boot)
    (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (nw nops : w64)
    (H0 : 0 ≤ sint.Z nw) (H31 : sint.Z nw < 2 ^ 31) (Hops : 0 ≤ sint.Z nops)
    (Hmul : sint.Z nw * sint.Z nops < 2 ^ 62)
    (HNs : prometheus.namesUnclaimed (cachekvProgram nw nops) cachekvNames)
    (HAs : addrsUnclaimed (cachekvProgram nw nops) [go!"127.0.0.1:23873"])
    -- (2026-11-03, the WAL's API, change 6; sweep repairs 1, W3/W4) the member's data directory, fresh at start (`dataDirsAbsent`)
    (HDs : dataDirsAbsent (cachekvProgram nw nops) [go!"cachekv.etcd"])
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    (HEnv : verifyEnvOff (cachekvProgram nw nops))
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ etcd_cache.premises (GF := putgetGF) (hG := heapAt hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([cachekvProgram nw nops], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #(W64 0) ∨ v = #(W64 1) ∨ v = #(W64 2) ∨ v = #(W64 3)) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  etcd_cache_adequate Hctx Hcec id ctxs boot Hbf Haf Hbuq Hrf Hdbo nw nops H0 H31 Hops Hmul
    HNs HAs HDs HEnv n Hprem σ g Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

end adequacy

#print axioms cachekv_Main
#print axioms etcd_cache_adequate
#print axioms etcd_cache_safe

end EtcdGrove
end Perennial

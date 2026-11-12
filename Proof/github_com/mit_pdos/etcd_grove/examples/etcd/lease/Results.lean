/-
The closed lease example's results (`examples/etcd/lease/etcd_lease.go`; 2026-11-02,
`notes/lease-ex-plan.md`), restated, with the trust
base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`leasekv_Main`** (`MainLinked.lean`): `Main` -- one etcd member started in
  process (`NewServer`, `Start`), its gRPC server (`v3rpc.Server`) listening at `127.0.0.1:23936`
  (`net.Listen`, `go gs.Serve(l)`), a client (`clientv3.New`), its `Leases()` and
  `TimeToLive(7)`, and a panic if the listing has a lease twice or the answer is about another lease
  -- returns: it does not panic. From
  `isPkgInit leasekv`, the right to listen on the address, the main thread's token and `Main`'s
  named premises (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/lease/Main.lean`).
* **`etcd_lease_safe`** (`Adequacy.lean`'s `etcd_lease_adequate`): the closed
  theorem. Every real execution of `n` steps of `leasekv`'s initialization followed by `Main()`,
  from a fresh state with one thread, has no stuck thread, no thread ended in a panic, and the main
  thread's result, if any, is `#()`; under hypotheses of D19a's kinds (`notes/decisions.md`,
  D19r), as putget's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.lease.Adequacy

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.lease.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `etcd_lease.wp_Main`). -/
theorem leasekv_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_lease.Main.spec (GF := GF) (hG := hG) :=
  etcd_lease.wp_Main

end results

section adequacy
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt
variable [go_gctx : GoGlobalContext]

/-- **The adequacy example is safe, in the operational semantics** (`etcd_lease_adequate`, see the
file header and `Adequacy.lean`). -/
theorem etcd_lease_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.lease.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC leasekvGF, ContextReadErrs (GF := leasekvGF) (hG := heapAtLkv hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC leasekvGF, ContextErrsClient (GF := leasekvGF) (hG := heapAtLkv hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_lease.BootFacts id ctxs boot)
    (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (Hlp : leasePeersOk)
    (HNs : prometheus.namesUnclaimed leasekvProgram leasekvNames)
    (HAs : addrsUnclaimed leasekvProgram [go!"127.0.0.1:23936"])
    -- (2026-11-03, the WAL's API, change 6; sweep repairs 1, W3/W4) the member's data directory, fresh at start (`dataDirsAbsent`)
    (HDs : dataDirsAbsent leasekvProgram [go!"leasekv.etcd"])
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    (HEnv : verifyEnvOff leasekvProgram)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC leasekvGF,
      ⊢ etcd_lease.premises (GF := leasekvGF) (hG := heapAtLkv hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([leasekvProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  etcd_lease_adequate Hctx Hcec id ctxs boot Hbf Haf Hbuq Hrf Hdbo Hlp HNs HAs HDs HEnv n Hprem σ g
    Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

end adequacy

#print axioms leasekv_Main
#print axioms etcd_lease_adequate
#print axioms etcd_lease_safe

end EtcdGrove
end Perennial

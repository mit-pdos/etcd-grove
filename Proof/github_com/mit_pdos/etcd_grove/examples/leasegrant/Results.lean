/-
The closed lease-grant example's results (`examples/leasegrant/leasegrant.go`; 2026-11-02,
`notes/lease-grant-plan.md`), restated, with the trust
base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`leasegrant_Main`** (`MainLinked.lean`): `Main` -- one etcd member started in
  process (`NewServer`, `Start`), its gRPC server (`v3rpc.Server`) listening at `127.0.0.1:23956`
  (`net.Listen`, `go gs.Serve(l)`), a client (`clientv3.New`), its `Grant(600)`
  and `Leases()`, and a panic unless the listing has the lease granted
  -- returns: it does not panic. From
  `isPkgInit leasegrant`, the right to listen on the address, the main thread's token and `Main`'s
  named premises (`Spec/github_com/mit_pdos/etcd_grove/examples/leasegrant/Main.lean`).
* **`leasegrant_safe`** (`Adequacy.lean`'s `leasegrant_adequate`): the closed
  theorem. Every real execution of `n` steps of `leasegrant`'s initialization followed by `Main()`,
  from a fresh state with one thread, has no stuck thread, no thread ended in a panic, and the main
  thread's result, if any, is `#()`; under hypotheses of D19a's kinds (`notes/decisions.md`,
  D19r), as putget's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.leasegrant.Adequacy

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.leasegrant.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `leasegrant.wp_Main`). -/
theorem leasegrant_Main [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    leasegrant.Main.spec (GF := GF) (hG := hG) :=
  leasegrant.wp_Main

end results

section adequacy
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp
variable [go_gctx : GoGlobalContext]

/-- **The adequacy example is safe, in the operational semantics** (`leasegrant_adequate`, see the
file header and `Adequacy.lean`). -/
theorem leasegrant_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.leasegrant.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC leasegrantGF, ContextReadErrs (GF := leasegrantGF) (hG := heapAtLgr hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC leasegrantGF, ContextErrsClient (GF := leasegrantGF) (hG := heapAtLgr hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : leasegrant.BootFacts id ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (Hlp : leasePeersOk) (Hlne : lease.leasesNoExpiry)
    (HNs : prometheus.namesUnclaimed leasegrantProgram leasegrantNames)
    (HAs : addrsUnclaimed leasegrantProgram [go!"127.0.0.1:23956"])
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC leasegrantGF,
      ⊢ leasegrant.premises (GF := leasegrantGF) (hG := heapAtLgr hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([leasegrantProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  leasegrant_adequate Hctx Hcec id ctxs boot Hbf Hck Haf Hbuq Hrf Hdbo Hlp Hlne HNs HAs n Hprem σ g
    Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

end adequacy

#print axioms leasegrant_Main
#print axioms leasegrant_adequate
#print axioms leasegrant_safe

end EtcdGrove
end Perennial

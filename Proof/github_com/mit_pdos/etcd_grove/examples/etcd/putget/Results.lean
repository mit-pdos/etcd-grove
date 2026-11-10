/-
The adequacy example's results (`examples/etcd/putget/etcd_putget.go`; item 9), restated, with the trust
base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`putget_Main`** (stage 2, 2026-10-18; `MainLinked.lean`): `Main` -- one etcd member started in
  process (`NewServer`, `Start`), its gRPC server (`v3rpc.Server`) listening at `127.0.0.1:23790`
  (`net.Listen`, `go gs.Serve(l)`), a client (`clientv3.New`), a `Put` of `k` with value `v`, a
  `Get` of `k`, and a panic unless the `Get` returned `v` -- returns: it does not panic. From
  `isPkgInit putget`, the right to listen on the address, the main thread's token and `Main`'s
  named premises (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/putget/Main.lean`).
* **`etcd_putget_safe`** (stage 3, 2026-10-18; `Adequacy.lean`'s `etcd_putget_adequate`): the closed
  theorem. Every real execution of `n` steps of `putget`'s initialization followed by `Main()`,
  from a fresh state with one thread, has no stuck thread, no thread ended in a panic, and the main
  thread's result, if any, is `#()`; under hypotheses of D19a's kinds (`notes/decisions.md`,
  D19r; the two marked ones it took until 2026-10-20, `EofFromIoInit` and
  `ClosedchanFromContextInit`, are theorems of Perennial's package facts since `init-facts`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putget.Adequacy

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.putget.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `etcd_putget.wp_Main`). -/
theorem putget_Main [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_putget.Main.spec (GF := GF) (hG := hG) :=
  etcd_putget.wp_Main

end results

section adequacy
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp trivialExts_hasExt
variable [go_gctx : GoGlobalContext]

/-- **The adequacy example is safe, in the operational semantics** (`etcd_putget_adequate`, see the
file header and `Adequacy.lean`). -/
theorem etcd_putget_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.putget.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF, ContextReadErrs (GF := putgetGF) (hG := heapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetGF, ContextErrsClient (GF := putgetGF) (hG := heapAt hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : etcd_putget.BootFacts id ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed putgetProgram putgetNames)
    (HAs : addrsUnclaimed putgetProgram [go!"127.0.0.1:23790"])
    -- (2026-11-03, the WAL's API, change 6; sweep repairs 1, W3/W4) the member's data directory, fresh at start (`dataDirsAbsent`)
    (HDs : dataDirsAbsent putgetProgram [go!"putget.etcd"])
    -- (sweep repairs 1, B4) `ETCD_VERIFY` off for the run
    (HEnv : verifyEnvOff putgetProgram)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ etcd_putget.premises (GF := putgetGF) (hG := heapAt hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([putgetProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 28) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  etcd_putget_adequate Hctx Hcec id ctxs boot Hbf Hck Haf Hbuq Hrf Hdbo HNs HAs HDs HEnv n Hprem σ g
    Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

end adequacy

#print axioms putget_Main
#print axioms etcd_putget_adequate
#print axioms etcd_putget_safe

end EtcdGrove
end Perennial

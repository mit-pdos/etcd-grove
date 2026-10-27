/-
The adequacy example's results (`examples/putget/putget.go`; item 9), restated, with the trust
base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`putget_Main`** (stage 2, 2026-10-18; `MainLinked.lean`): `Main` -- one etcd member started in
  process (`NewServer`, `Start`), its gRPC server (`v3rpc.Server`) listening at `127.0.0.1:23790`
  (`net.Listen`, `go gs.Serve(l)`), a client (`clientv3.New`), a `Put` of `k` with value `v`, a
  `Get` of `k`, and a panic unless the `Get` returned `v` -- returns: it does not panic. From
  `isPkgInit putget`, the right to listen on the address, the main thread's token and `Main`'s
  named premises (`Spec/github_com/mit_pdos/etcd_grove/examples/putget/Main.lean`).
* **`putget_safe`** (stage 3, 2026-10-18; `Adequacy.lean`'s `putget_adequate`): the closed
  theorem. Every real execution of `n` steps of `putget`'s initialization followed by `Main()`,
  from a fresh state with one thread, has no stuck thread, no thread ended in a panic, and the main
  thread's result, if any, is `#()`; under hypotheses of D19a's kinds (`notes/decisions.md`,
  D19r; the two marked ones it took until 2026-10-20, `EofFromIoInit` and
  `ClosedchanFromContextInit`, are theorems of Perennial's package facts since `init-facts`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget.Adequacy

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.putget.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `putget.wp_Main`). -/
theorem putget_Main [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    putget.Main.spec (GF := GF) (hG := hG) :=
  putget.wp_Main

end results

section adequacy
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp
variable [go_gctx : GoGlobalContext]

/-- **The adequacy example is safe, in the operational semantics** (`putget_adequate`, see the
file header and `Adequacy.lean`). -/
theorem putget_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.putget.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF, ContextReadErrs (GF := putgetGF) (hG := heapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetGF, ContextErrsClient (GF := putgetGF) (hG := heapAt hG lctx))
    (id : w64) (bootLog : List EntryM) (Hbf : putget.BootFacts id bootLog)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hdbo : storage.dbOpensOk)
    (HNs : prometheus.namesUnclaimed putgetProgram putgetNames)
    (HAs : addrsUnclaimed putgetProgram [go!"127.0.0.1:23790"])
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ putget.premises (GF := putgetGF) (hG := heapAt hG lctx) n id bootLog)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([putgetProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 31) (Hwb : n + 7 ≤ backend.wbInit) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  putget_adequate Hctx Hcec id bootLog Hbf Hck Haf Hbuq Hdbo HNs HAs n Hprem σ g
    Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn Hwb

end adequacy

#print axioms putget_Main
#print axioms putget_adequate
#print axioms putget_safe

end EtcdGrove
end Perennial

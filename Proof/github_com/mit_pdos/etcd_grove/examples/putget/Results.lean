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
  thread's result, if any, is `#()`; under hypotheses of D19a's kinds and the two marked ones,
  `EofFromIoInit` and `ClosedchanFromContextInit` (false under the current Perennial pin: the
  proposed Perennial changes make them theorems; `notes/decisions.md`, D19r).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
attribute [local instance] disk_op disk_model disk_semantics disk_interp
variable [go_gctx : GoGlobalContext]

/-- **The adequacy example is safe, in the operational semantics** (`putget_adequate`, see the
file header and `Adequacy.lean`). -/
theorem putget_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.putget.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [ErrorStringLeaf] [RpctypesEtcdErrorMethods] [context.ErrorStringIsError]
    [context.DeadlineExceededIsError] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF, ContextReadErrs (GF := putgetGF) (hG := heapAt hG lctx))
    (Hms : v3rpc.ServerMethodSets)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (id : w64) (bootLog : List EntryM) (Hbf : putget.BootFacts id bootLog)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hdbo : storage.dbOpensOk)
    (HNs : prometheus.namesUnclaimed putgetProgram putgetNames)
    (HAs : addrsUnclaimed putgetProgram [go!"127.0.0.1:23790"])
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ putget.premises (GF := putgetGF) (hG := heapAt hG lctx) n id bootLog)
    (HEof : ∀ hG : HeapGS .hasLC putgetGF, putget.EofFromIoInit (GF := putgetGF) (hG := heapAt hG lctx))
    (HCc : ∀ hG : HeapGS .hasLC putgetGF,
      putget.ClosedchanFromContextInit (GF := putgetGF) (hG := heapAt hG lctx))
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : g.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([putgetProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 31) (Hwb : n + 7 ≤ backend.wbInit) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  putget_adequate Hctx Hms hAs id bootLog Hbf Hck Haf Hbuq Hdbo HNs HAs n Hprem HEof HCc σ g
    Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn Hwb

end adequacy

#print axioms putget_Main
#print axioms putget_adequate
#print axioms putget_safe

end EtcdGrove
end Perennial

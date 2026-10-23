/-
The watch example's results (`examples/watchkv/watchkv.go`; D23), restated, with the trust base
of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`watchkv_Main`** (`Link.lean`'s `watchkv.wp_Main`): `Main(nw, nops)` -- the Puts picked, one
  etcd member started in process, a client with etcd's default configuration, a prefix watch from revision `1`, `nw`
  writers, the watch read up to the highest successful revision, and a check that panics unless
  the watched events are exactly the writes -- does not panic and returns `Ok`, `Failed` or
  `WatchEnded`. From `isPkgInit watchkv`, the right to listen on `127.0.0.1:23872`, the main
  thread's token and `Main`'s named premises (`Spec/github_com/mit_pdos/etcd_grove/examples/watchkv/Main.lean`).
* **`watch_safe`** (`Adequacy.lean`'s `watch_adequate`): the closed theorem. Every real execution of
  `n` steps of `watchkv`'s initialization followed by `Main(nw, nops)`, from a fresh state with one
  thread, has no stuck thread, no thread ended in a panic (so the check never failed), and the main
  thread's result, if any, is `0`, `1` or `2`; under putget's hypotheses at watchkv's configuration
  and the ones `Adequacy.lean`'s header lists beyond them.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Adequacy

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.watchkv.Assumptions]

/-- **`Main` does not panic** (`Link.lean`'s `watchkv.wp_Main`). -/
theorem watchkv_Main [go_etcd_io.etcd.cache.v3.Assumptions] [Float64ToInt64Semantics]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    watchkv.Main.spec (GF := GF) (hG := hG) :=
  watchkv.wp_Main

end results

section adequacy
attribute [local instance] disk_op disk_model disk_semantics disk_interp
variable [go_gctx : GoGlobalContext]

/-- **The watch example is safe, in the operational semantics** (`watch_adequate`, see the file
header and `Adequacy.lean`). -/
theorem watch_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.watchkv.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [_root_.Perennial.errors.Assumptions] [_root_.Perennial.fmt.Assumptions]
    [go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [ErrorStringLeaf] [ErrorStringNoGRPCStatus] [RpctypesEtcdErrorMethods]
    [context.ErrorStringIsError] [context.DeadlineExceededIsError] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putgetGF, ContextReadErrs (GF := putgetGF) (hG := heapAt hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putgetGF, ContextErrsClient (GF := putgetGF) (hG := heapAt hG lctx))
    (Hms : v3rpc.ServerMethodSets)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (id : w64) (bootLog : List EntryM) (Hbf : putget.BootFacts id bootLog)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hdbo : storage.dbOpensOk)
    (nw nops : w64)
    (H0 : 0 ≤ sint.Z nw) (H31 : sint.Z nw < 2 ^ 31) (Hops : 0 ≤ sint.Z nops)
    (Hmul : sint.Z nw * sint.Z nops < 2 ^ 62)
    (HNs : prometheus.namesUnclaimed (watchkvProgram nw nops) watchkvNames)
    (HAs : addrsUnclaimed (watchkvProgram nw nops) [go!"127.0.0.1:23872"])
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putgetGF,
      ⊢ watchkv.premises (GF := putgetGF) (hG := heapAt hG lctx) n id bootLog)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : g.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([watchkvProgram nw nops], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 29) (Hwb : n + 7 ≤ backend.wbInit) :
    (∀ v t2', t2 = Val v :: t2' → v = #(W64 0) ∨ v = #(W64 1) ∨ v = #(W64 2)) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  watch_adequate Hctx Hcec Hms hAs id bootLog Hbf Hck Haf Hbuq Hdbo nw nops H0 H31 Hops Hmul
    HNs HAs n Hprem σ g Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn Hwb

end adequacy

#print axioms watchkv_Main
#print axioms watch_adequate
#print axioms watch_safe

end EtcdGrove
end Perennial

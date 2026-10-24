/-
The KV-workload linearizability instance's results (`examples/linkvtxn/linkvtxn.go`; linkv-txn
stage G), restated, with the trust base of each printed in the build log (`#print axioms`).
Lean-first (no Rocq counterpart).

* **`linkvtxn_Main`** (`Link.lean`'s `linkvtxn.wp_Main`): `Main(clients, ops)` -- one etcd member
  started in process, a client with etcd's default configuration, `Check(cli, clients, ops, 0)`
  (`lintest.Run` with the model of etcd's KV, `Apply` over the client: gets, lists, puts, deletes,
  transactions; porcupine's checker), and a panic if porcupine answers `Illegal` -- does not panic
  and returns `Ok` or `Unknown`. From `isPkgInit linkvtxn`, the right to listen on
  `127.0.0.1:23796`, the main thread's token and `Main`'s named premises
  (`Spec/github_com/mit_pdos/etcd_grove/examples/linkvtxn/Main.lean`).
* **`linkvtxn_safe`** (`Adequacy.lean`'s `linkvtxn_adequate`): the closed theorem. Every real
  execution of `n` steps of `linkvtxn`'s initialization followed by `Main(clients, ops)`, from a
  fresh state with one thread, has no stuck thread, no thread ended in a panic (so never
  "linkvtxn: porcupine found the history not linearizable"), and the main thread's result, if any,
  is `Ok` or `Unknown`; under linkv's hypotheses (`linkvtxn_safe`) at linkvtxn's configuration.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Adequacy

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]
variable [NaInvG GF]

/-- **`Main` does not panic** (`Link.lean`'s `linkvtxn.wp_Main`). -/
theorem linkvtxn_Main [go_etcd_io.etcd.cache.v3.Assumptions] [Float64ToInt64Semantics]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [ErrorStringLeaf] :
    linkvtxn.Main.spec (GF := GF) (hG := hG) :=
  linkvtxn.wp_Main

end results

section adequacy
attribute [local instance] disk_op disk_model disk_semantics disk_interp
variable [go_gctx : GoGlobalContext]

/-- **The linearizability instance is safe, in the operational semantics** (`linkvtxn_adequate`,
see the file header and `Adequacy.lean`). -/
theorem linkvtxn_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [ErrorStringLeaf] [RpctypesEtcdErrorMethods] [context.ErrorStringIsError]
    [context.DeadlineExceededIsError] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC linkvtxnGF, ContextReadErrs (GF := linkvtxnGF) (hG := linkvtxnHeapAt hG lctx))
    (Hms : v3rpc.ServerMethodSets)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (id : w64) (bootLog : List EntryM) (Hbf : putget.BootFacts id bootLog)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hdbo : storage.dbOpensOk)
    (clients ops : w64)
    (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (HNs : prometheus.namesUnclaimed (linkvtxnProgram clients ops) linkvtxnNames)
    (HAs : addrsUnclaimed (linkvtxnProgram clients ops) [go!"127.0.0.1:23796"])
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC linkvtxnGF,
      ⊢ linkvtxn.premises (GF := linkvtxnGF) (hG := linkvtxnHeapAt hG lctx) n id bootLog)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : g.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([linkvtxnProgram clients ops], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 31) (Hwb : n + 7 ≤ backend.wbInit) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  linkvtxn_adequate Hctx Hms hAs id bootLog Hbf Hck Haf Hbuq Hdbo clients ops Hc0 Hc31 Hops Hmul
    HNs HAs n Hprem σ g Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn Hwb

end adequacy

#print axioms linkvtxn_Main
#print axioms linkvtxn_adequate
#print axioms linkvtxn_safe

end EtcdGrove
end Perennial

/-
The Kubernetes etcd3 store's linearizability instance's results
(`examples/k8setcd3/k8setcd3.go`; stage 6g of `notes/k8s-etcd3-plan.md`), restated, with the
trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`k8setcd3_Main`** (`Link.lean`'s `k8setcd3.wp_Main`): `Main(clients, ops)` -- one etcd member
  started in process, a kubernetes client configured for one attempt per call, the seed objects,
  the Kubernetes etcd3 store over the client (`etcd3.New`, the driver's codec, versioner,
  transformer and decoder), `Check(s, st0, clients, ops, 0)` (`lintest.Run` with the driver's Go
  model of the store, `Apply` over the store: `Create`, `Get`, `Delete`, `GuaranteedUpdate`;
  porcupine's checker), and a panic if porcupine answers `Illegal` -- does not panic and returns
  `Ok` or `Unknown`. From `isPkgInit k8setcd3`, the right to listen on `127.0.0.1:23896`, the main
  thread's token and `Main`'s named premises
  (`Spec/github_com/mit_pdos/etcd_grove/examples/k8setcd3/Main.lean`).
* **`k8setcd3_safe`** (`Adequacy.lean`'s `k8setcd3_adequate`): the closed theorem. Every real
  execution of `n` steps of `k8setcd3`'s initialization followed by `Main(clients, ops)`, from a
  fresh state with one thread, has no stuck thread, no thread ended in a panic (so never
  "k8setcd3: porcupine found the history not linearizable"), and the main thread's result, if
  any, is `Ok` or `Unknown`; under k8setcd3's hypotheses at k8setcd3's configuration, the
  Kubernetes packages' semantics assumptions (the method-set facts `objTyOk` and
  `storageErrTyOk` follow from them).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Adequacy

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]
variable [NaInvG GF]

/-- **`Main` does not panic** (`Link.lean`'s `k8setcd3.wp_Main`). -/
theorem k8setcd3_Main [go_etcd_io.etcd.cache.v3.Assumptions] [Float64ToInt64Semantics]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    k8setcd3.Main.spec (GF := GF) (hG := hG) :=
  k8setcd3.wp_Main

end results

section adequacy
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp
variable [go_gctx : GoGlobalContext]

/-- **The Kubernetes etcd3 store's linearizability instance is safe, in the operational semantics** (`k8setcd3_adequate`,
see the file header and `Adequacy.lean`). -/
theorem k8setcd3_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [k8s_io.apiserver.pkg.storage.etcd3.Assumptions] [k8s_io.apimachinery.pkg.runtime.Assumptions]
    [k8s_io.apimachinery.pkg.runtime.schema.Assumptions] [k8s_io.apiserver.pkg.storage.Assumptions]
    [k8s_io.apiserver.pkg.storage.value.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC k8setcd3GF, ContextReadErrs (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List Draft.LogEntry)
    (Hbf : putget.BootFacts id ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hdbo : storage.dbOpensOk)
    (clients ops : w64)
    (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (HNs : prometheus.namesUnclaimed (k8setcd3Program clients ops) k8setcd3Names)
    (HAs : addrsUnclaimed (k8setcd3Program clients ops) [go!"127.0.0.1:23896"])
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC k8setcd3GF,
      ⊢ k8setcd3.premises (GF := k8setcd3GF) (hG := k8setcd3HeapAt hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([k8setcd3Program clients ops], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 31) (Hwb : n + 7 ≤ backend.wbInit) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  k8setcd3_adequate Hctx id ctxs boot Hbf Hck Haf Hbuq Hdbo clients ops Hc0 Hc31 Hops
    Hmul HNs HAs n Hprem σ g Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn Hwb

end adequacy

#print axioms k8setcd3_Main
#print axioms k8setcd3_adequate
#print axioms k8setcd3_safe

end EtcdGrove
end Perennial

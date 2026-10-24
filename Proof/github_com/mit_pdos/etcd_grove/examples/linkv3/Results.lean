/-
The three-member linearizability instance's results (`examples/linkv3/linkv3.go`; D20, D21),
restated, with the trust base of each printed in the build log (`#print axioms`). Lean-first (no
Rocq counterpart).

* **`linkv3_Main`** (`Link.lean`'s `linkv3.wp_Main`): `Main(clients, ops)` -- three etcd members
  started in process (putget3's `startMember`), a client to the first (`127.0.0.1:23811`)
  with etcd's default configuration, linkv's `Check(cli, clients, ops, 0)`, and a panic if
  porcupine answers `Illegal` -- does not panic and returns `Ok` or `Unknown`. From
  `isPkgInit linkv3`, the right to listen on the four addresses, the main thread's token and
  `Main`'s named premises (`Spec/github_com/mit_pdos/etcd_grove/examples/linkv3/Main.lean`).
* **`linkv3_safe`** (`Adequacy.lean`'s `linkv3_adequate`): the closed theorem. Every real execution
  of `n` steps of `linkv3`'s initialization followed by `Main(clients, ops)`, from a fresh state with
  one thread, has no stuck thread, no thread ended in a panic (so never "linkv3: porcupine found
  the history not linearizable"), and the main thread's result, if any, is `Ok` or `Unknown`;
  under putget3's hypotheses (`putget3_safe`) at linkv3's configuration and `Run`'s bounds on
  `clients` and `ops` (`linkv_safe`'s).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3.Adequacy

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3.Assumptions]
variable [NaInvG GF]

/-- **`Main` does not panic** (`Link.lean`'s `linkv3.wp_Main`). -/
theorem linkv3_Main [go_etcd_io.etcd.cache.v3.Assumptions] [Float64ToInt64Semantics]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [ErrorStringLeaf] [ErrorStringNotWriter] :
    linkv3.Main.spec (GF := GF) (hG := hG) :=
  linkv3.wp_Main

end results

section adequacy
attribute [local instance] disk_op disk_model disk_semantics disk_interp
variable [go_gctx : GoGlobalContext]

/-- **The three-member linearizability instance is safe, in the operational semantics**
(`linkv3_adequate`, see the file header and `Adequacy.lean`). -/
theorem linkv3_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [ErrorStringLeaf] [ErrorStringNotWriter] [RpctypesEtcdErrorMethods] [context.ErrorStringIsError]
    [context.DeadlineExceededIsError] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC linkvGF, ContextReadErrs (GF := linkvGF) (hG := linkvHeapAt hG lctx))
    (Hms : v3rpc.ServerMethodSets)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (Hbf : linkv3.BootFacts id₁ id₂ id₃ bootLog)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hdbo : storage.dbOpensOk)
    (clients ops : w64)
    (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (HNs : prometheus.namesUnclaimed (linkv3Program clients ops) linkv3Names)
    (HAs : addrsUnclaimed (linkv3Program clients ops) linkv3Addrs)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC linkvGF,
      ⊢ linkv3.premises (GF := linkvGF) (hG := linkvHeapAt hG lctx) n id₁ id₂ id₃ bootLog)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : g.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([linkv3Program clients ops], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 31) (Hwb : n + 7 ≤ backend.wbInit) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  linkv3_adequate Hctx Hms hAs id₁ id₂ id₃ bootLog Hbf Hck Haf Hbuq Hdbo clients ops Hc0 Hc31 Hops Hmul
    HNs HAs n Hprem σ g Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn Hwb

end adequacy

#print axioms linkv3_Main
#print axioms linkv3_adequate
#print axioms linkv3_safe

end EtcdGrove
end Perennial

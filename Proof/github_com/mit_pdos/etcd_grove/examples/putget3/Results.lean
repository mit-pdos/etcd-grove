/-
putget3's results (`examples/putget3/putget3.go`; D21 stage M5, 2026-10-19), restated, with the
trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`putget3_Main`** (`MainLinked.lean`): `Main` -- three etcd members started in process
  (`startMember`: `NewServer`, the raft handler served on the member's peer listener
  (`RaftHandler`, `http.Serve`), `Start`), the first's gRPC server listening at `127.0.0.1:23791`, a
  client, a `Put` of `k` with value `v`, a `Get` of `k`, and a panic unless the `Get` returned `v`
  -- returns: it does not panic (`Spec/github_com/mit_pdos/etcd_grove/examples/putget3/Main.lean`).
* **`putget3_safe`** (`Adequacy.lean`'s `putget3_adequate`): the closed theorem, putget's for the
  three-member program, under hypotheses of D19a's kinds (without the two marked ones it took
  until 2026-10-20, `EofFromIoInit` and `ClosedchanFromContextInit`: now theorems).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget3.Adequacy

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.putget3.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `putget3.wp_Main`). -/
theorem putget3_Main [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] [ErrorStringLeaf] [ErrorStringNotWriter] :
    putget3.Main.spec (GF := GF) (hG := hG) :=
  putget3.wp_Main

end results

section adequacy
attribute [local instance] disk_op disk_model disk_semantics disk_interp
variable [go_gctx : GoGlobalContext]

/-- **putget3 is safe, in the operational semantics** (`putget3_adequate`, see the
file header and `Adequacy.lean`). -/
theorem putget3_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.putget3.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [ErrorStringLeaf] [ErrorStringNotWriter] [RpctypesEtcdErrorMethods] [context.ErrorStringIsError]
    [context.DeadlineExceededIsError] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC putget3GF, ContextReadErrs (GF := putget3GF) (hG := heapAt3 hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC putget3GF, ContextErrsClient (GF := putget3GF) (hG := heapAt3 hG lctx))
    (Hms : v3rpc.ServerMethodSets)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (Hbf : putget3.BootFacts id₁ id₂ id₃ bootLog)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hdbo : storage.dbOpensOk)
    (HNs : prometheus.namesUnclaimed putget3Program putget3Names)
    (HAs : addrsUnclaimed putget3Program putget3Addrs)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC putget3GF,
      ⊢ putget3.premises (GF := putget3GF) (hG := heapAt3 hG lctx) n id₁ id₂ id₃ bootLog)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : g.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([putget3Program], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 31) (Hwb : n + 7 ≤ backend.wbInit) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  putget3_adequate Hctx Hcec Hms hAs id₁ id₂ id₃ bootLog Hbf Hck Haf Hbuq Hdbo HNs HAs n Hprem σ g
    Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn Hwb

end adequacy

#print axioms putget3_Main
#print axioms putget3_adequate
#print axioms putget3_safe

end EtcdGrove
end Perennial

/-
**`compactkv`** (the client's `kv.Compact`, 2026-11-01): putgetc's file, for putgetc under
compaction pressure (`common.StartCompactingServer`, revision mode, retention 1; five rounds of a
put of the round's key, a client compaction at the revision before it, a get of the key);
putgetc's and putget's history below is the originals'.

The adequacy example's results (`examples/compactkv/compactkv.go`; item 9), restated, with the trust
base of each printed in the build log (`#print axioms`). Lean-first (no Rocq counterpart).

* **`compactkv_Main`** (stage 2, 2026-10-18; `MainLinked.lean`): `Main` -- one etcd member started in
  process (`NewServer`, `Start`), its gRPC server (`v3rpc.Server`) listening at `127.0.0.1:23794`
  (`net.Listen`, `go gs.Serve(l)`), a client (`clientv3.New`), five rounds of a `Put` of the
  round's key with value `v`, a `Compact` at the revision before it and a `Get` of the key, each with
  a panic unless the `Get` returned `v` -- returns: it does not panic. From
  `isPkgInit compactkv`, the right to listen on the address, the main thread's token and `Main`'s
  named premises (`Spec/github_com/mit_pdos/etcd_grove/examples/compactkv/Main.lean`).
* **`compactkv_safe`** (stage 3, 2026-10-18; `Adequacy.lean`'s `compactkv_adequate`): the closed
  theorem. Every real execution of `n` steps of `compactkv`'s initialization followed by `Main()`,
  from a fresh state with one thread, has no stuck thread, no thread ended in a panic, and the main
  thread's result, if any, is `#()`; under hypotheses of D19a's kinds (`notes/decisions.md`,
  D19r; the two marked ones it took until 2026-10-20, `EofFromIoInit` and
  `ClosedchanFromContextInit`, are theorems of Perennial's package facts since `init-facts`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.compactkv.Adequacy

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.compactkv.Assumptions]

/-- **`Main` does not panic** (`MainLinked.lean`'s `compactkv.wp_Main`). -/
theorem compactkv_Main [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    compactkv.Main.spec (GF := GF) (hG := hG) :=
  compactkv.wp_Main

end results

section adequacy
attribute [local instance] trivialExts trivialExtsSemantics trivialExtsInterp
variable [go_gctx : GoGlobalContext]

/-- **The adequacy example is safe, in the operational semantics** (`compactkv_adequate`, see the
file header and `Adequacy.lean`). -/
theorem compactkv_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.compactkv.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC compactkvGF, ContextReadErrs (GF := compactkvGF) (hG := heapAtCkv hG lctx))
    (Hcec : ∀ hG : HeapGS .hasLC compactkvGF, ContextErrsClient (GF := compactkvGF) (hG := heapAtCkv hG lctx))
    (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (Hbf : compactkv.BootFacts id ctxs boot)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hrf : grpcRepliesFit) (Hdbo : storage.diskOk)
    (HNs : prometheus.namesUnclaimed compactkvProgram compactkvNames)
    (HAs : addrsUnclaimed compactkvProgram [go!"127.0.0.1:23794"])
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC compactkvGF,
      ⊢ compactkv.premises (GF := compactkvGF) (hG := heapAtCkv hG lctx) n id ctxs boot)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : σ.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([compactkvProgram], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 31) :
    (∀ v t2', t2 = Val v :: t2' → v = #()) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  compactkv_adequate Hctx Hcec id ctxs boot Hbf Hck Haf Hbuq Hrf Hdbo HNs HAs n Hprem σ g
    Hlctx Hinit Hthreads κs t2 σ2 Hsteps Hn

end adequacy

#print axioms compactkv_Main
#print axioms compactkv_adequate
#print axioms compactkv_safe

end EtcdGrove
end Perennial

/-
The partitioned three-member instance's results (`examples/linkv3p/linkv3p.go`; the partition
plan, `notes/partition-plan.md`), restated, with the trust base of each printed in the build log
(`#print axioms`). Lean-first (no Rocq counterpart).

* **`linkv3p_Main`** (`Link.lean`'s `linkv3p.wp_Main`): `Main(clients, ops, sched)` -- three etcd
  members started in process and served (`startMember`), a one-attempt client to each
  (`127.0.0.1:2383{1,2,3}`), the partitioner forked on the schedule `sched` (the links between
  members cut and mended, in both directions, as its steps say, with etcd's own
  `CutPeer`/`MendPeer`), linkv's `Check` with each operation through a random member, and a panic
  if porcupine answers `Illegal` -- does not panic and returns `Ok` or `Unknown`, **for every
  schedule** (`sched ↦*□ steps`, any `steps`). From `isPkgInit linkv3p`, the right to listen on
  the six addresses, the main thread's token and `Main`'s named premises
  (`Spec/github_com/mit_pdos/etcd_grove/examples/linkv3p/Main.lean`).
* **`linkv3p_safe`** (`Adequacy.lean`'s `linkv3p_adequate`): the closed theorem. Every real
  execution of `n` steps of `linkv3p`'s initialization followed by `Main(clients, ops, sched)`,
  the schedule built as a slice literal of any list of steps, from a fresh state with one
  thread, has no stuck thread, no thread ended in a panic (so never "linkv3p: porcupine found
  the history not linearizable"), and the main thread's result, if any, is `Ok` or `Unknown`;
  under linkv3's hypotheses (`linkv3_safe`) at linkv3p's configuration, v3rpc's method sets as
  an instance, `Run`'s bounds on `clients` and `ops` (`linkv_safe`'s) and the schedule's length
  below `2^63`.

What the theorem says of partitions: the network model (`Transport.Start`'s axiom) lets any
message be lost, so the proofs of raft and of etcd's server never needed delivery; this program
is the one in which messages *are* lost, on the schedule's say, with clients at every member,
and the theorem is that every history it produces is still linearizable (D24, the
transport's remotes: the hooks' axioms take a member of a new cluster).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Adequacy

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]
variable [NaInvG GF]

/-- **`Main` does not panic, for every schedule** (`Link.lean`'s `linkv3p.wp_Main`). -/
theorem linkv3p_Main [go_etcd_io.etcd.cache.v3.Assumptions] [Float64ToInt64Semantics]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    linkv3p.Main.spec (GF := GF) (hG := hG) :=
  linkv3p.wp_Main

end results

section adequacy
attribute [local instance] disk_op disk_model disk_semantics disk_interp
variable [go_gctx : GoGlobalContext]

/-- **The partitioned three-member instance is safe, in the operational semantics**
(`linkv3p_adequate`, see the file header and `Adequacy.lean`). -/
theorem linkv3p_safe [lctx : GoLocalContext] [sem : go.Semantics]
    [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]
    [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
    [Float64ToInt64Semantics] [go_etcd_io.etcd.client.v3.DialWithBalancerBody]
    [ErrorStringLeaf] [RpctypesEtcdErrorMethods] [context.ErrorStringIsError]
    [context.DeadlineExceededIsError] [log.NewModel]
    (Hctx : ∀ hG : HeapGS .hasLC linkvGF, ContextReadErrs (GF := linkvGF) (hG := linkvHeapAt hG lctx))
    (Hms : v3rpc.ServerMethodSets)
    (hAs : errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty)
    (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (Hbf : linkv3p.BootFacts id₁ id₂ id₃ bootLog)
    (Hck : ckptEffectsOk) (Haf : authRecordsFit)
    (Hbuq : apply.backendUnderQuota) (Hnoc : mvcc.backendNoCompaction)
    (clients ops : w64)
    (Hc0 : 0 ≤ sint.Z clients) (Hc31 : sint.Z clients < 2 ^ 31) (Hops : 0 ≤ sint.Z ops)
    (Hmul : sint.Z clients * sint.Z ops < 2 ^ 60)
    (steps : List github_com.mit_pdos.etcd_grove.examples.linkv3p.Step)
    (Hsteps : steps.length < 2 ^ 63)
    (HNs : prometheus.namesUnclaimed (linkv3pProgram clients ops steps) linkv3pNames)
    (HAs : addrsUnclaimed (linkv3pProgram clients ops steps) linkv3pAddrs)
    (n : Nat)
    (Hprem : ∀ hG : HeapGS .hasLC linkvGF,
      ⊢ linkv3p.premises (GF := linkvGF) (hG := linkvHeapAt hG lctx) n id₁ id₂ id₃ bootLog)
    (σ : state) (g : GlobalState) (Hlctx : σ.goState.goLctx = lctx) (Hinit : IsInit σ)
    (Hthreads : g.threads = 1)
    (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps' : RealNsteps n ([linkv3pProgram clients ops steps], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hn : n + 2 ≤ 2 ^ 31) (Hwb : n + 7 ≤ backend.wbInit) :
    (∀ v t2', t2 = Val v :: t2' → v = #(go!"Ok") ∨ v = #(go!"Unknown")) ∧
    (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
    (∀ v, Val v ∈ t2 → v.isPanic = false) :=
  linkv3p_adequate Hctx Hms hAs id₁ id₂ id₃ bootLog Hbf Hck Haf Hbuq Hnoc clients ops Hc0 Hc31 Hops
    Hmul steps Hsteps HNs HAs n Hprem σ g Hlctx Hinit Hthreads κs t2 σ2 Hsteps' Hn Hwb

end adequacy

#print axioms linkv3p_Main
#print axioms linkv3p_adequate
#print axioms linkv3p_safe

end EtcdGrove
end Perennial

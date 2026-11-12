/-
Lean-first (no Rocq counterpart). Trace-check's layer D (the harness, 2026-11-12;
`notes/trace-check-design.md` §2.3).

`(*Cluster).app(r)` (`examples/raft/tracecheck/concurrent.go`): replica `r`'s application goroutine.
It ticks its node, handles each `Ready` (`handleReady`), advances the node, then hands each of the
`Ready`'s messages, cloned, to the network (`send`), until the stop channel is closed. It starts with
the node idle (its driver state not handling a `Ready`), its durable state, its configuration view
(`ViewOk`), the whole of its liveness (`nodeRunning 1`), its storage's metadata, a share `q` of the
network join's adders' right, and the fork's thread token (`wp_fork_tok_body`), which it keeps through
every `send` (each deposits it and gets a fresh one: `wp_fork_tok_self`). At the stop it returns the
liveness and the adders' share through the `apps` join's `Done`, and exits with a thread token.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.HarnessDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [MemStorReg GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

attribute [local instance] memStorageModel

/-- What an `app` returns to the `apps` join at its stop: its node (of id `id`, the replica `r`'s)
with the whole of its liveness, and its share of the network join's adders' right. -/
def appDone (c : Loc) (W : TcW) (r : Loc) (id : w64) (q : Qp) : IProp GF :=
  iprop(∃ n : Loc, r.[github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.creplica, go!"node"]
      ↦□ nodeIface n ∗ isNode n W.cl tcRaftN id ∗ nodeRunning n W.cl tcRaftN 1 ∗
    njAdder tcNetN (c.[G.Cluster, go!"net"]) W.nj q)

/-- See the file header. -/
abbrev Cluster.app.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (W : TcW) (r n ms : Loc) (γs : MemStorNames) (id : w64)
    (st : NodeDriverState) (v : ConfigView) (hs0 : HardStateM) (q : Qp),
  st.handling = none → st.storage = memStorIface ms → ViewOk st.delivered v →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
      tcWorld c W ∗ repInfo W.cl r id n ms γs ∗ repOwn r ∗ memStorMeta ms γs hs0 ∗
      nodeDriver n W.cl tcRaftN st ∗ raftState W.cl id st.durable ∗ nodeConfig n W.cl tcRaftN v ∗
      nodeRunning n W.cl tcRaftN 1 ∗
      sync.join.ownDone (c.[G.Cluster, go!"apps"]) (appDone c W r id q) ∗
      njAdder tcNetN (c.[G.Cluster, go!"net"]) W.nj q ∗ threadTok }}
    (App (Val (c @!! go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster.ty @!! go!"app"))
      (Val #r))
  {{ RET #(); threadTok }}

end spec

end TraceCheck
end EtcdGrove
end Perennial

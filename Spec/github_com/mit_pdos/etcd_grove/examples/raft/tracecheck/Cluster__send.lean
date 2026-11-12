/-
Lean-first (no Rocq counterpart). Trace-check's layer D (the harness, 2026-11-12;
`notes/trace-check-design.md` §2.4).

`(*Cluster).send(src, m, delay, drop)` (`examples/raft/tracecheck/concurrent.go`): one network
goroutine for the message `m` (a clone of a message the replica `src` of id `sid` handed out), which
sleeps, then steps `m` into its destination's node (`node.Step`, with a timeout) or drops it
(`ReportUnreachable` to the sender). The caller (an `app`) brings what `stepIn_intro` takes of the
message: its `sentMsg`, credits and token (`trTok`), and the clone owned with no responses; and its
share of the network join's adders' right with its thread token, which the goroutine's slot holds
(the `go` gives the caller a fresh one: `wp_fork_tok_self`). It returns both. The message's token
also says it is no `MsgSnap` (`trTok_type`), so `ReportSnapshot` is never called.
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- See the file header. -/
abbrev Cluster.send.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (W : TcW) (src : Loc) (sid : w64) (ml : Loc)
    (st : MsgSt) (delay : time.Duration) (drop : Bool) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
      tcWorld c W ∗ repNode W.cl src sid ∗
      msgPtsC ml (DFrac.own 1) (DFrac.own 1) true ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ ∗
      sentMsg W.cl tcRaftN sid st ∗ msgCredits W.cl tcRaftN st ∗ trTok W.cl st ∗
      njAdder tcNetN (c.[G.Cluster, go!"net"]) W.nj q ∗ threadTok }}
    (App (App (App (App (Val (c @!! go.GoType.PointerType
        github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster.ty @!! go!"send"))
      (Val #src)) (Val #ml)) (Val #delay)) (Val #drop))
  {{ RET #(); njAdder tcNetN (c.[G.Cluster, go!"net"]) W.nj q ∗ threadTok }}

end spec

end TraceCheck
end EtcdGrove
end Perennial

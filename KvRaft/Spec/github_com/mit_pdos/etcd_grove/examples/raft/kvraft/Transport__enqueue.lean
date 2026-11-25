/-
`t.enqueue(p, m)` (`examples/raft/kvraft/transport.go`): the message `m` queued for the peer `p`
(`p.queue`, a bag channel of `qElem F pid`, `TransportDefs.lean`), or, if the queue is full, dropped
(`dropped`). The caller gives the message away with its fact (`qElem F pid m`).
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.TransportDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Net go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev Transport.enqueue.spec : Prop :=
  ∀ (F : KvFacts GF) (t : Loc) (γ : Cluster) (N : Namespace) (id : w64) (n : NodeH) (p : Loc)
    (pid : w64) (a : GoString) (m : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      isTransportCore F t γ N id n ∗ isPeer F p pid a ∗ qElem F pid m }}
    (App (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport.ty
      @!! go!"enqueue")) (Val #p)) (Val #m))
  {{ RET #(); True }}

end spec

end kvraft
end EtcdGrove
end Perennial

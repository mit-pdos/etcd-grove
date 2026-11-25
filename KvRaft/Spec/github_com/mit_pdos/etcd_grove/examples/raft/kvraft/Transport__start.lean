/- Lean-first (no Rocq counterpart).

`t.start(node)` (`examples/raft/kvraft/transport.go`): the transport `t` (as `newTransport` left it:
its id and stats, its peers, its node field unset) gets the node `n` (the interface over `*node`), and
a sender goroutine per peer (`Transport.runPeer`); then its fixed part holds (`isTransportCore`),
with the step law the caller gives (raft's message layer at the protocol's facts, `stepLaw`).
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
abbrev Transport.start.spec : Prop :=
  ∀ (F : KvFacts GF) (t : Loc) (γ : Cluster) (N : Namespace) (id : w64) (n : NodeH) (sp : Loc)
    (et ed : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      t.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport, go!"id"] ↦□ id ∗
      t.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport, go!"stats"] ↦□ sp ∗
      (∃ v : GoInterface, t.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport, go!"node"] ↦ v) ∗
      isStats sp ∗ isPeers F t ∗ isNode n γ N id ∗ ⌜Cluster.trace γ = none⌝ ∗
      (∃ (sc : Loc) (γsc : ChanNames), isTransportStop t sc γsc) ∗
      globalAddr net.errTimeout ↦□ et ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport.ty
      @!! go!"start")) (Val #(interface.mkOk (go.GoType.PointerType node.ty) #n.loc)))
  {{ RET #(); isTransportCore F t γ N id n }}

end spec

end kvraft
end EtcdGrove
end Perennial

/-
`t.dial(p)` (`examples/raft/kvraft/transport.go`): a connection to the peer `p` (id `pid`, address
`a` with the protocols `kvP F pid`/`kvQ F pid`, `isPeerAddr`), as a peer: the hello byte
`helloPeer` written (within `writeTimeout`), or `nil` (the dial or the write failed). With a
connection, the dialer's end: its writer's token after the hello byte (`sendTok cn false (kvP F
pid) [helloPeerB]`, for the frames `runPeer` writes), its reader's token (nothing read), and
`connIs cn` (to close it).
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
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev Transport.dial.spec : Prop :=
  ∀ (F : KvFacts GF) (t : Loc) (γ : Cluster) (N : Namespace) (id : w64) (n : NodeH) (p : Loc)
    (pid : w64) (a : GoString) (et ed : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      isTransportCore F t γ N id n ∗ isPeerAddr F p pid a ∗ globalAddr net.errTimeout ↦□ et ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport.ty
      @!! go!"dial")) (Val #p))
  {{ (c : GoInterface), RET #c;
      ⌜c = interface.nil⌝ ∨
      ∃ cn, net.isConn (GF := GF) c cn false a ∗ sendTok cn false (kvP F pid) [helloPeerB] ∗
        recvTok cn false (kvQ F pid) [] ∗ connIs cn }}

end spec

end kvraft
end EtcdGrove
end Perennial

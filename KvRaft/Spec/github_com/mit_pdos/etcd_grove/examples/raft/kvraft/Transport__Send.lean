/-
`t.Send(ms)` (`examples/raft/kvraft/transport.go`): each message of `ms` handed to its peer's queue
(`enqueue`), or dropped (`dropped`) if its destination is no peer the transport knows. The caller
gives the messages away, each with its fact (`sendElem F m`: `F.msgOk`); the slice
is only read.
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

/-- A message `Send` takes: owned at any fractions, with its fact. -/
def sendElem (F : KvFacts GF) (m : Loc) : IProp GF :=
  iprop(∃ (dq dqe : DFrac) (cap : Bool) (st : MsgSt) (src : w64),
    msgPtsC m dq dqe cap st ∗ F.msgOk src st)

/-- See the file header. -/
abbrev Transport.Send.spec : Prop :=
  ∀ (F : KvFacts GF) (t : Loc) (γ : Cluster) (N : Namespace) (id : w64) (n : NodeH) (msl : GoSlice)
    (dqs : DFrac) (ms : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft ∗
      isTransportCore F t γ N id n ∗ isPeers F t ∗ msl ↦*{dqs} ms ∗ [∗list] m ∈ ms, sendElem F m }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Transport.ty
      @!! go!"Send")) (Val #msl))
  {{ RET #(); msl ↦*{dqs} ms }}

end spec

end kvraft
end EtcdGrove
end Perennial

/-
`t.dropped(m)` (`examples/raft/kvnet/transport.go`): the message `m` was not sent: counted, and the
node told (`ReportUnreachable` of its destination; `ReportSnapshot` failure for a snapshot). The
message is only read (its `To` and `Type`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TransportDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev Transport.dropped.spec : Prop :=
  ∀ (F : KvFacts GF) (t : Loc) (γ : Cluster) (N : Namespace) (id : w64) (n : NodeH) (m : Loc)
    (dq dqe : DFrac) (cap : Bool) (st : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
      isTransportCore F t γ N id n ∗ msgPtsC m dq dqe cap st }}
    (App (Val (t @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Transport.ty
      @!! go!"dropped")) (Val #m))
  {{ RET #(); msgPtsC m dq dqe cap st }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial

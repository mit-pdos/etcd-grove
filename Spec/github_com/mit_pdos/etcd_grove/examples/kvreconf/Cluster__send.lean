/- Lean-first (no Rocq counterpart).

`c.send(from, ms)` (cluster.go): replica `from`'s messages, as its `Ready` hands them out
(`sendSpec`: each at `readyDq`, sent by `from`, with its credits), each handed to the network
(`deliver`) as a fresh copy (`copyMsg`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

/-- See the file header. -/
abbrev Cluster.send.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (c : Loc) (src : w64) (msl : GoSlice) (ms : List QMsg),
  {{ isClusterC γr vs c ∗ repKnown γr src ∗
      ownSlice msl (ms.map QMsg.loc) (DFrac.own 1) ∗
      [∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γr.cluster kvrRaftN src q.st ∗
        msgCredits γr.cluster kvrRaftN q.st }}
    (App (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"send")) (Val #src))
      (Val #msl))
  {{ RET #(); True }}

end spec

end kvreconf
end EtcdGrove
end Perennial

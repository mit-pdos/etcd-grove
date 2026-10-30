/- Lean-first (no Rocq counterpart).

`c.step(src, dst, m)` (cluster.go): the message `m`, sent by `sid` (`sentMsg`, with its credits),
stepped on its target `dst` (the running replica of `m`'s `To`), which takes it for good: the
message wholly owned, without responses, with its `Entries` capacity (what `stepIn_intro` takes);
then the fate of the message (unreachable within the timeout, a snapshot's) reported to the
sender's node `src` (any running replica).
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
abbrev Cluster.step.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (c : Loc) (sid : w64) (src dst ml : Loc) (st : MsgSt),
  {{ isClusterC γr vs c ∗ isRep γr vs sid src ∗ isRep γr vs st.msg.To' dst ∗
      msgPtsC ml (DFrac.own 1) (DFrac.own 1) true { st with resps := [] } ∗
      sentMsg γr.cluster kvrRaftN sid st ∗ msgCredits γr.cluster kvrRaftN st }}
    (App (App (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"step")) (Val #src))
      (Val #dst)) (Val #ml))
  {{ RET #(); True }}

end spec

end kvreconf
end EtcdGrove
end Perennial

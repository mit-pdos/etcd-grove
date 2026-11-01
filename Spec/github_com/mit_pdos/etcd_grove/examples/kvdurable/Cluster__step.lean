/- Lean-first (no Rocq counterpart).

`c.step(src, dst, m)` (cluster.go): the message `m`, sent by `sid` (`sentMsg`, with its credits),
stepped on its target `dst` (an incarnation of `m`'s `To`), which takes it for good: the message
wholly owned, without responses, with its `Entries` capacity (what `stepIn_intro` takes); then the
fate of the message (unreachable within the timeout, a snapshot's) reported to the sender's node
`src` (an incarnation of `sid`). A crashed incarnation's node is stopped: it takes nothing, and its
reports are no-ops.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev Cluster.step.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (sid : w64) (src dst ml : Loc)
    (st : MsgSt),
  {{ isClusterC γ vs dir c ∗ isRep γ vs dir sid src ∗ isRep γ vs dir st.msg.To' dst ∗
      msgPtsC ml (DFrac.own 1) (DFrac.own 1) true { st with resps := [] } ∗
      sentMsg γ.r.cluster kdRaftN sid st ∗ msgCredits γ.r.cluster kdRaftN st }}
    (App (App (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"step")) (Val #src))
      (Val #dst)) (Val #ml))
  {{ RET #(); True }}

end spec

end kvdurable
end EtcdGrove
end Perennial

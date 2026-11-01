/- Lean-first (no Rocq counterpart).

`c.send(from, ms)` (cluster.go): replica `from`'s messages, as its `Ready` hands them out
(`sendSpec`: each at `readyDq`, sent by `from`, with its credits), each handed to the network
(`deliver`) as a fresh copy (`copyMsg`), from the sender's current incarnation (`c.replica(from)`).
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
abbrev Cluster.send.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (src : w64) (msl : GoSlice)
    (ms : List QMsg),
  {{ isClusterC γ vs dir c ∗ repKnown γ src ∗
      ownSlice msl (ms.map QMsg.loc) (DFrac.own 1) ∗
      [∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ.r.cluster kdRaftN src q.st ∗
        msgCredits γ.r.cluster kdRaftN q.st }}
    (App (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"send")) (Val #src))
      (Val #msl))
  {{ RET #(); True }}

end spec

end kvdurable
end EtcdGrove
end Perennial

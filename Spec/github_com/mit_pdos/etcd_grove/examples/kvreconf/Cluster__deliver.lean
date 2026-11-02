/- Lean-first (no Rocq counterpart).

`c.deliver(src, m)` (cluster.go): the network, for the message `m` of the running replica `src`
(`sid`), sent by `sid` (`sentMsg`, with its credits) and wholly owned as `step` takes it: it drops
`m` (`dropped`: its target unknown, or by chance), steps it later from another goroutine, or now,
and then perhaps a second time (a fresh copy, `copyMsg`, with the credits made persistent:
`msgCredits_copy`, `γ.dup = true`).
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
abbrev Cluster.deliver.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (c : Loc) (sid : w64) (src ml : Loc) (st : MsgSt),
  {{ isClusterC γr vs c ∗ isRep γr vs sid src ∗
      msgPtsC ml (DFrac.own 1) (DFrac.own 1) true { st with resps := [] } ∗
      sentMsg γr.cluster kvrRaftN sid st ∗ msgCredits γr.cluster kvrRaftN st }}
    (App (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"deliver")) (Val #src))
      (Val #ml))
  {{ RET #(); True }}

end spec

end kvreconf
end EtcdGrove
end Perennial

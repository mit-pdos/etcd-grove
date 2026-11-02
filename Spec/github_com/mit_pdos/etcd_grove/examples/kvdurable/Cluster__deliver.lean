/- Lean-first (no Rocq counterpart).

`c.deliver(src, m)` (cluster.go): the network, for the message `m` of an incarnation `src` of replica
`sid`, sent by `sid` (`sentMsg`, with its credits) and wholly owned as `step` takes it: it drops `m`
(`dropped`: its target unknown, or by chance), steps it later from another goroutine, or now, and
then perhaps a second time (a fresh copy, `copyMsg`, with the credits made persistent:
`msgCredits_copy`, `γ.dup = true`).
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
abbrev Cluster.deliver.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (sid : w64) (src ml : Loc)
    (st : MsgSt),
  {{ isClusterC γ vs dir c ∗ isRep γ vs dir sid src ∗
      msgPtsC ml (DFrac.own 1) (DFrac.own 1) true { st with resps := [] } ∗
      sentMsg γ.r.cluster kdRaftN sid st ∗ msgCredits γ.r.cluster kdRaftN st }}
    (App (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"deliver")) (Val #src))
      (Val #ml))
  {{ RET #(); True }}

end spec

end kvdurable
end EtcdGrove
end Perennial

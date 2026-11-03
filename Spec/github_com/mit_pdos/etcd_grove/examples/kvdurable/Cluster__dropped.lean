/- Lean-first (no Rocq counterpart).

`c.dropped(src, m)` (cluster.go): the network drops the message `m` (holding `st`, at any
fractions) of an incarnation `src` of replica `sid`, and tells `src`'s node so (`ReportUnreachable`,
and `ReportSnapshot` of a snapshot). It only reads `m`, which it gives back.
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
abbrev Cluster.dropped.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (sid : w64) (src ml : Loc)
    (dq dqe : DFrac) (cap : Bool) (st : MsgSt),
  {{ isClusterC γ vs dir c ∗ isRep γ vs dir sid src ∗ msgPtsC ml dq dqe cap st }}
    (App (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"dropped")) (Val #src))
      (Val #ml))
  {{ RET #(); msgPtsC ml dq dqe cap st }}

end spec

end kvdurable
end EtcdGrove
end Perennial

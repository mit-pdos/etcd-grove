/- Lean-first (no Rocq counterpart).

`c.dropped(src, m)` (cluster.go): the network drops the message `m` (holding `st`, at any
fractions) of the running replica `src`, and tells `src`'s node so (`ReportUnreachable`, and
`ReportSnapshot` of a snapshot). It only reads `m`, which it gives back.
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
abbrev Cluster.dropped.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (c : Loc) (sid : w64) (src ml : Loc) (dq dqe : DFrac)
    (cap : Bool) (st : MsgSt),
  {{ isClusterC γr vs c ∗ isRep γr vs sid src ∗ msgPtsC ml dq dqe cap st }}
    (App (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"dropped")) (Val #src))
      (Val #ml))
  {{ RET #(); msgPtsC ml dq dqe cap st }}

end spec

end kvreconf
end EtcdGrove
end Perennial

/- Lean-first (no Rocq counterpart).

`c.randomChange()` (reconf.go): a random configuration change, owned by the caller: a
`ConfChange`, or a `ConfChangeV2` (the empty one, or one to three single changes) of one of the three
defined transitions. Its transition is defined for its changes (`ccTransOk`, `Rule.lean`), which is
what a proposal of it needs (`kvr_ccAu`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Rule

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
abbrev Cluster.randomChange.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (c : Loc),
  {{ isClusterC γr vs c }}
    (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"randomChange")) (Val #()))
  {{ (cc : GoInterface) (o : ConfChangeIM), RET #cc;
      ownConfChangeI cc (DFrac.own 1) (some o) ∗ ⌜ccTransOk o⌝ }}

end spec

end kvreconf
end EtcdGrove
end Perennial

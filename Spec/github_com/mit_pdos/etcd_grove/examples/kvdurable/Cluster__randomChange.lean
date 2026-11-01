/- Lean-first (no Rocq counterpart). kvreconf's.

`c.randomChange()` (reconf.go): a random configuration change, owned by the caller: a
`ConfChange`, or a `ConfChangeV2` (the empty one, or one to three single changes) of one of the three
defined transitions. Its transition is defined for its changes (`ccTransOk`, `Rule.lean`), which is
what a proposal of it needs (`kd_ccAu`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Rule

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
abbrev Cluster.randomChange.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc),
  {{ isClusterC γ vs dir c }}
    (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"randomChange")) (Val #()))
  {{ (cc : GoInterface) (o : ConfChangeIM), RET #cc;
      ownConfChangeI cc (DFrac.own 1) (some o) ∗ ⌜kvreconf.ccTransOk o⌝ }}

end spec

end kvdurable
end EtcdGrove
end Perennial

-- The copy for the part `RaftNoAx/` of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/Cluster__sender.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

`c.sender(from)` (cluster.go): replica `from`'s transport (`sendSpec`, what `newReplica` takes), for
a started `from` (`repKnown`: `c.replica(from)`, which each send looks the sender up by, is then
some incarnation of it).
-/
module

public import RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev Cluster.sender.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (src : w64),
  {{ isClusterC γ vs dir c ∗ repKnown (GF := GF) γ src }}
    (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"sender")) (Val #src))
  {{ (f : GoFunc), RET #f; sendSpec γ src f }}

end spec

end raft_kvdurable
end EtcdGrove
end Perennial

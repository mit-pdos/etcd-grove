/- Lean-first (no Rocq counterpart).

`c.sender(from)` (cluster.go): replica `from`'s transport (`sendSpec`, what `newReplica` takes), for
a started `from` (`repKnown`: `c.replica(from)`, which each send looks the sender up by, is then
some incarnation of it).
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
abbrev Cluster.sender.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (src : w64),
  {{ isClusterC γ vs dir c ∗ repKnown γ src }}
    (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"sender")) (Val #src))
  {{ (f : GoFunc), RET #f; sendSpec γ src f }}

end spec

end kvdurable
end EtcdGrove
end Perennial

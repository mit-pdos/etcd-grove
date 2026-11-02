/- Lean-first (no Rocq counterpart).

`c.startNew()` (cluster.go): under `c.mu`, a replica of a fresh id (the id's durable state at
`RaftState.init` and its slot out of the join authority, `joinAuth_join`; no file yet: its
invariant allocated at `none`, the writer's half to `start`), started by `Cluster.start`; `ok` false
once `maxReplicas` were started.
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
abbrev Cluster.startNew.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc),
  {{ isClusterC γ vs dir c }}
    (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"startNew")) (Val #()))
  {{ (id : w64) (ok : Bool), RET (PairV #id #ok);
      ⌜ok = true⌝ -∗ repKnown γ id }}

end spec

end kvdurable
end EtcdGrove
end Perennial

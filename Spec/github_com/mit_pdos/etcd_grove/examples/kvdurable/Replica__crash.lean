/- Lean-first (no Rocq counterpart).

`r.crash()` (kv.go): under `dmu`, `crashed` set: from now on nothing writes the file, and the writer's
half of the file's variable (at the file's contents `o` and durable state `S`) comes out of `dmu`
for the restarter; then `stop`, whose `node.Stop` gives the id's slot back (`nodeVacant`).
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
abbrev Replica.crash.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r : Loc),
  {{ repStop γ vs dir id r }}
    (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"crash")) (Val #()))
  {{ RET #(); nodeVacant γ.r.cluster id ∗ ∃ (S : RaftState) (o : Option StorFile), kdWriter γ id S o }}

end spec

end kvdurable
end EtcdGrove
end Perennial

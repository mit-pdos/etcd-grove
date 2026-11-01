/- Lean-first (no Rocq counterpart). kvreconf's, without the stopper's mode.

`c.all()` (cluster.go): every replica's current incarnation (as `c.replicas` held it under `c.mu`:
running, `isRep`, though it may have crashed since), of a started id (`repKnown`); there is one at
least (the voters).

`specStop` (2026-11-01, the stopper; `Stop`'s): with the crasher's token, which it leaves in the lock
(so no restart is under way, and none can start), it also takes every current incarnation's
`repStop` out of the lock.
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
abbrev Cluster.all.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc),
  {{ isClusterC γ vs dir c }}
    (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"all")) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ rs : List Loc, sl ↦* rs ∗ ⌜rs ≠ []⌝ ∗
      [∗list] r ∈ rs, ∃ id, isRep γ vs dir id r ∗ repKnown γ id }}

/-- See the file header. -/
abbrev Cluster.all.specStop : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc),
  {{ isClusterC γ vs dir c ∗ crasher γ }}
    (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"all")) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ rs : List Loc, sl ↦* rs ∗
      [∗list] r ∈ rs, ∃ id, repStop γ vs dir id r }}

end spec

end kvdurable
end EtcdGrove
end Perennial

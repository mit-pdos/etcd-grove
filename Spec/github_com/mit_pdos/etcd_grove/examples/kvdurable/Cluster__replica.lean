/- Lean-first (no Rocq counterpart).

`c.replica(id)` (cluster.go): the current incarnation of replica `id` (`isRep`: running, though it
may have crashed since), or `nil` if there is none; for a started `id` (`known`, with `repKnown`)
never `nil`.

`specPin` (2026-11-01, the crasher): `Cluster.restart`'s call, with the crasher's token. The result
is the id's current incarnation (`curRep`, the fragment of the map of the current incarnations),
with its stopper-and-crasher share (`repStop`), both out of the lock, the token left in their place.
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
abbrev Cluster.replica.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (id : w64) (known : Bool),
  {{ isClusterC γ vs dir c ∗ (if known then repKnown γ id else iprop(True)) }}
    (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"replica")) (Val #id))
  {{ (r : Loc), RET #r; ⌜r = null ∧ known = false⌝ ∨ isRep γ vs dir id r }}

/-- See the file header. -/
abbrev Cluster.replica.specPin : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (id : w64),
  {{ isClusterC γ vs dir c ∗ repKnown γ id ∗ crasher γ }}
    (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"replica")) (Val #id))
  {{ (r : Loc), RET #r; curRep γ id r ∗ repStop γ vs dir id r }}

end spec

end kvdurable
end EtcdGrove
end Perennial

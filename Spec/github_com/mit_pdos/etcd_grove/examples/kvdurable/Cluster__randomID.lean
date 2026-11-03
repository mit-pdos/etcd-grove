/- Lean-first (no Rocq counterpart). kvreconf's.

`c.randomID(cs, add)` (reconf.go): the id a random change names: one of the conf state `cs`'s
(read-only, possibly `nil`), a running replica's, or, if `add`, sometimes a fresh replica's, started
now (`startNew`). Any id: nothing is promised of it.
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
abbrev Cluster.randomID.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c csp : Loc) (cs : ConfStateM) (add : Bool),
  {{ isClusterC γ vs dir c ∗ csOpt csp DFrac.discard cs }}
    (App (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"randomID")) (Val #csp))
      (Val #add))
  {{ (id : w64), RET #id; True }}

end spec

end kvdurable
end EtcdGrove
end Perennial

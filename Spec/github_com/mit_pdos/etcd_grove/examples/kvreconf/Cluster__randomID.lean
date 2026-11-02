/- Lean-first (no Rocq counterpart).

`c.randomID(cs, add)` (reconf.go): the id a random change names: one of the conf state `cs`'s
(read-only, possibly `nil`), a running replica's, or, if `add`, sometimes a fresh replica's, started
now (`startNew`). Any id: nothing is promised of it.
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
abbrev Cluster.randomID.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (c csp : Loc) (cs : ConfStateM) (add : Bool),
  {{ isClusterC γr vs c ∗ csOpt csp DFrac.discard cs }}
    (App (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"randomID")) (Val #csp))
      (Val #add))
  {{ (id : w64), RET #id; True }}

end spec

end kvreconf
end EtcdGrove
end Perennial

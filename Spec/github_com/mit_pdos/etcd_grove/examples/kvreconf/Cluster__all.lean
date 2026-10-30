/- Lean-first (no Rocq counterpart).

`c.all()` (cluster.go): every replica (each running, `isRep`); with the stopper's token (`own`),
also every replica's stop token, the token then spent (`γr.stp` set).
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
abbrev Cluster.all.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (c : Loc) (own : Bool),
  {{ isClusterC γr vs c ∗ (if own then stopper γr else iprop(True)) }}
    (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"all")) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ rs : List Loc, sl ↦* rs ∗ ⌜rs ≠ []⌝ ∗
      ([∗list] r ∈ rs, ∃ id, isRep γr vs id r) ∗
      (if own then iprop(ghostVar γr.stp (1 : Qp).half true ∗ [∗list] r ∈ rs, repStop γr vs r)
       else iprop(True)) }}

end spec

end kvreconf
end EtcdGrove
end Perennial

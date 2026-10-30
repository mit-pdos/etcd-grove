/- Lean-first (no Rocq counterpart).

`c.Read(key)` (cluster.go): logically atomic over the store's map, returning `m key`: a read by
read index at random members, retried until one answers.
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
abbrev Cluster.Read.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (c : Loc) (key : List w8) (Φ : List w8 → IProp GF),
  (key.length : Int) < 2 ^ 61 →
  {{ isClusterC γr vs c ∗
      AU <{ ∃∃ (x : KVMap), rkvVal γr x }> @ kvrMask, ∅ <{ rkvVal γr x, COMM Φ (x key) }> }}
    (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"Read")) (Val #key))
  {{ (res : List w8), RET #res; Φ res }}

end spec

end kvreconf
end EtcdGrove
end Perennial

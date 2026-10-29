/- Lean-first (no Rocq counterpart).

`c.Read(key)` (cluster.go): a linearizable read by read index at random members, retried until one
answers: the value is `key`'s in a history at least the client's lower bound `L0` (kv's `KV.Read`,
without a read credit: raft's `ReadIndex` takes none).
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
  ∀ (γr : RNames) (vs : List w64) (c : Loc) (key : List w8) (L0 : List (List w8)),
  (key.length : Int) < 2 ^ 61 →
  {{ isClusterC γr vs c ∗ kvLb γr L0 }}
    (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"Read")) (Val #key))
  {{ (x : List w8), RET #x; ∃ L, kvLb γr L ∗ ⌜L0 <+: L ∧ x = kvFold L key⌝ }}

end spec

end kvreconf
end EtcdGrove
end Perennial

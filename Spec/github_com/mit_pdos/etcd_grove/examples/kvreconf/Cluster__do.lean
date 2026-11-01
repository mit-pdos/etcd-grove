/- Lean-first (no Rocq counterpart).

`c.do(kind, key, val)` (cluster.go): one operation, logically atomic (kv's `KV.do`): a fresh id
from the cluster (`nextOp` under `c.mu`), the datum minted with its slot holding the client's atomic
update, proposed at random members until one answers. The update takes effect when the datum's
first entry commits; `do` returns the key's value after it.
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
abbrev Cluster.do.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (c : Loc) (kind : w8) (key val : List w8)
    (Φ : List w8 → IProp GF),
  (key.length : Int) < 2 ^ 61 → (val.length : Int) < 2 ^ 61 →
  {{ isClusterC γr vs c ∗
      AU <{ ∃∃ (x : KVMap), rkvVal γr x }> @ kvrMask, ∅
        <{ rkvVal γr (kvNext kind key val x), COMM Φ (kvNext kind key val x key) }> }}
    (App (App (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"do")) (Val #kind)) (Val #key)) (Val #val))
  {{ (res : List w8), RET #res; Φ res }}

end spec

end kvreconf
end EtcdGrove
end Perennial

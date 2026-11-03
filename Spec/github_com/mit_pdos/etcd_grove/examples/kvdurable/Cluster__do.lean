/- Lean-first (no Rocq counterpart). kvreconf's.

`c.do(kind, key, val)` (cluster.go): one operation, logically atomic (kv's `KV.do`): a fresh id
from the cluster (`nextOp` under `c.mu`), the datum minted with its slot holding the client's atomic
update, proposed at random members until one answers. The update takes effect when the datum's
first entry commits; `do` returns the key's value after it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open kvreconf (KVMap kvUpd kvNext)
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
abbrev Cluster.do.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (kind : w8) (key val : List w8)
    (Φ : List w8 → IProp GF),
  (key.length : Int) < 2 ^ 61 → (val.length : Int) < 2 ^ 61 →
  {{ isClusterC γ vs dir c ∗
      AU <{ ∃∃ (x : KVMap), rkvVal γ x }> @ kdMask, ∅
        <{ rkvVal γ (kvNext kind key val x), COMM Φ (kvNext kind key val x key) }> }}
    (App (App (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"do")) (Val #kind)) (Val #key)) (Val #val))
  {{ (res : List w8), RET #res; Φ res }}

end spec

end kvdurable
end EtcdGrove
end Perennial

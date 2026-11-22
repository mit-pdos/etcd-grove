-- The copy for the part `RaftNoAx/` of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/Cluster__do.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart). kvreconf's.

`c.do(kind, key, val)` (cluster.go): one operation, logically atomic (kv's `KV.do`): a fresh id
from the cluster (`nextOp` under `c.mu`), the datum minted with its slot holding the client's atomic
update, proposed at random members until one answers. The update takes effect when the datum's
first entry commits; `do` returns the key's value after it.
-/
module

public import RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvdurable

open raft_kvreconf (KVMap kvUpd kvNext)
open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]

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

end raft_kvdurable
end EtcdGrove
end Perennial

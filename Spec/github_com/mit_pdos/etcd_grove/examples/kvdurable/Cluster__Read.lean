/- Lean-first (no Rocq counterpart). kvreconf's.

`c.Read(key)` (cluster.go): logically atomic over the store's map, returning `m key`: a read by
read index at random members, retried until one answers.
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
abbrev Cluster.Read.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) (key : List w8)
    (Φ : List w8 → IProp GF),
  (key.length : Int) < 2 ^ 61 →
  {{ isClusterC γ vs dir c ∗
      AU <{ ∃∃ (x : KVMap), rkvVal γ x }> @ kdMask, ∅ <{ rkvVal γ x, COMM Φ (x key) }> }}
    (App (Val (c @!! go.GoType.PointerType kClusterTy @!! go!"Read")) (Val #key))
  {{ (res : List w8), RET #res; Φ res }}

end spec

end kvdurable
end EtcdGrove
end Perennial

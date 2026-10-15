/-
`raftpb.ConfChange.AsV2` (`raftpb/confchange.go:56`): the V2 change of a legacy one.
Lean-first (no Rocq counterpart); see `InvConfChangeMsg.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvConfChangeMsg

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `c.AsV2()`: a `ConfChangeV2` with the one change `{Type: c.Type, NodeId: c.NodeId}` (a fresh
slice), `c`'s `Context` (the same slice) and the `Auto` transition. -/
abbrev raftpb.ConfChange.AsV2.spec : Prop :=
  ∀ (c : raftpb.ConfChange),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val (c @!! raftpb.ConfChange.ty @!! go!"AsV2")) (Val #()))
  {{ (v : raftpb.ConfChangeV2), RET #v;
      ⌜v.Transition' = W32 0 ∧ v.Context' = c.Context'⌝ ∗
      v.Changes' ↦* [({ Type' := c.Type', NodeId' := c.NodeId' } : raftpb.ConfChangeSingle)] }}

end spec

end EtcdGrove
end Perennial

/-
`(*ConfChange).AsV2` (`raftpb/confchange.go:58`). Port of the old
`Spec/go_etcd_io/raft/v3/raftpb/ConfChange__AsV2.lean` to raft v3.7 (pointer receiver, getters,
`Enum()`, `new(...)`; stage R1).
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb

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

/-- `c.AsV2()` of a `*ConfChange` holding `m`: a fresh `*ConfChangeV2` holding `m.asV2` -- the one
change `{Type: c.GetType().Enum(), NodeId: new(c.GetNodeId())}` (a fresh slice holding a fresh
`*ConfChangeSingle`), `c`'s `Context` (the same slice, its bytes read-only, shared) and the
`Auto` transition (a nil field). -/
abbrev raftpb.ConfChange.AsV2.spec : Prop :=
  ∀ (c : Loc) (dq : DFrac) (m : CCV1M),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ ownCCV1 c dq m }}
    (App (Val (c @!! go.GoType.PointerType raftpb.ConfChange.ty @!! go!"AsV2")) (Val #()))
  {{ (v : Loc), RET #v; ownCCV1 c dq m ∗ ownCCV2 v (DFrac.own 1) m.asV2 }}

end spec

end EtcdGrove
end Perennial

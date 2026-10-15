/-
`raftpb.ConfChange.AsV1` (`raftpb/confchange.go:67`). Lean-first (no Rocq counterpart); see `InvConfChangeMsg.lean`.
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

/-- `c.AsV1()` returns `(c, true)`. -/
abbrev raftpb.ConfChange.AsV1.spec : Prop :=
  ∀ (c : raftpb.ConfChange),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val (c @!! raftpb.ConfChange.ty @!! go!"AsV1")) (Val #()))
  {{ RET (PairV #c #true); True }}

end spec

end EtcdGrove
end Perennial

/-
`raftpb.ConfChangeV2.AsV1` (`raftpb/confchange.go:75`). Lean-first (no Rocq counterpart); see `InvConfChangeMsg.lean`.
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

/-- `c.AsV1()` returns `(ConfChange{}, false)`. -/
abbrev raftpb.ConfChangeV2.AsV1.spec : Prop :=
  ∀ (c : raftpb.ConfChangeV2),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val (c @!! raftpb.ConfChangeV2.ty @!! go!"AsV1")) (Val #()))
  {{ RET (PairV #(zero_val raftpb.ConfChange) #false); True }}

end spec

end EtcdGrove
end Perennial

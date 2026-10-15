/-
`(*ConfChangeV2).AsV1` (`raftpb/confchange.go:77`). Port of the old spec to raft v3.7 (pointer
receiver, a nil `*ConfChange` where gogoproto's returned the zero value; stage R1).
-/
module

public import Raft37.Proof.go_etcd_io.raft.v3.InvPb

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

/-- `c.AsV1()` returns `(nil, false)`. -/
abbrev raftpb.ConfChangeV2.AsV1.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val (c @!! go.GoType.PointerType raftpb.ConfChangeV2.ty @!! go!"AsV1")) (Val #()))
  {{ RET (PairV #(null : Loc) #false); True }}

end spec

end EtcdGrove
end Perennial

/-
`(*ConfChangeV2).AsV2` (`raftpb/confchange.go:74`). Port of the old spec to raft v3.7 (pointer
receiver; stage R1).
-/
module

public import Proof.go_etcd_io.raft.v3.InvPb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `c.AsV2()` returns `c`. -/
abbrev raftpb.ConfChangeV2.AsV2.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val (c @!! go.GoType.PointerType raftpb.ConfChangeV2.ty @!! go!"AsV2")) (Val #()))
  {{ RET #c; True }}

end spec

end EtcdGrove
end Perennial

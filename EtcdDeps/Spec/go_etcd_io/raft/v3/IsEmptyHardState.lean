/-
`raft.IsEmptyHardState(st)` (node.go), of etcd's raft dependency (raft v3.7). Lean-first (no
Rocq counterpart); see `InvRaftMsg.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftMsg
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

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

/-- `IsEmptyHardState(st)`: whether `st` is nil or has every field 0 (against the package's
`emptyState`). -/
abbrev IsEmptyHardState.spec : Prop :=
  ∀ (st : Loc) (hs : HardStateModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ hardStateAt st hs }}
    (App (Val (@! go_etcd_io.raft.v3.IsEmptyHardState)) (Val #st))
  {{ (r : Bool), RET #r; ⌜r = true ↔ hs = HardStateModel.empty⌝ }}

end spec

end EtcdGrove
end Perennial

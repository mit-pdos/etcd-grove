/-
`raft.isHardStateEqual(a, b)` (node.go), of etcd's raft dependency (raft v3.7). Lean-first (no
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

/-- `isHardStateEqual(a, b)`: whether the two hard states have the same term, vote and
commit. -/
abbrev isHardStateEqual.spec : Prop :=
  ∀ (a b : Loc) (ha hb : HardStateModel),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ hardStateAt a ha ∗
      hardStateAt b hb }}
    (App (App (Val (@! go_etcd_io.raft.v3.isHardStateEqual)) (Val #a)) (Val #b))
  {{ (r : Bool), RET #r; ⌜r = true ↔ ha = hb⌝ }}

end spec

end EtcdGrove
end Perennial

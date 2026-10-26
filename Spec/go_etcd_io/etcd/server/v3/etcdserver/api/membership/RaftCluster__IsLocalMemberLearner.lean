/-
`membership.RaftCluster.IsLocalMemberLearner` (`cluster.go`: under the lock, the local member's
`IsLearner`; `c.lg.Panic` if the members map has no entry for `c.localID`). Lean-first (no Rocq
counterpart); 2026-10-26: the server's `IsLearner`, the interceptors' check.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.membership.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `c.IsLocalMemberLearner()` (`c` a cluster whose local member stays in its members map,
`membership.localKept`) returns some boolean: the map has an entry for `c.localID` (`rcLockInv`'s
`rcLocalIn`), so its `c.lg.Panic` branch is not taken. -/
abbrev membership.RaftCluster.IsLocalMemberLearner.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership ∗ membership.localKept c }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster.ty @!! go!"IsLocalMemberLearner")) (Val #()))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial

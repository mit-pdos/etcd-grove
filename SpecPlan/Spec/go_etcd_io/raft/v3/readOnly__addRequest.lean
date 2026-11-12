/-
## `(*readOnly).addRequest(commitIndex, req)` (internal)

**Users**: `stepLeader`'s `MsgReadIndex` under `ReadOnlySafe` (`raft.go:2162`), and
`releasePendingReadIndexMessages`. Snippet `raftlog/readindex.go` (`ReqReadIndexQuorum`). Mirrors the
code; the request pointer is fresh (`&readIndexRequest{...}`), the message is not owned by the
queue (the caller keeps what it knows of it). **Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/readOnly__addRequest.lean`.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiLog

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) Queue a read request at the commit index. -/
def readOnly.addRequest.spec : Prop :=
  ∀ (ro : Loc) (rs : ReadOnlyState) (c : w64) (req : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ readOnly ro rs }}
    (App (App (Val (ro @!! go.GoType.PointerType go_etcd_io.raft.v3.readOnly.ty @!! go!"addRequest")) (Val #c)) (Val #req))
  {{ RET #(); ∃ p : Loc, readOnly ro { rs with pending := rs.pending ++ [(p, req, c)] } }}

end spec
end Raft
end EtcdGrove
end Perennial

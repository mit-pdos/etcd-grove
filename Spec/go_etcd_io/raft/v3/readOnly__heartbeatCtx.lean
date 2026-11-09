/-
## `(*readOnly).heartbeatCtx()` (internal)

**Users**: `bcastHeartbeat` (`raft.go:725`), `stepLeader`'s `MsgReadIndex` (`raft.go:2164`).
Mirrors the code. **Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/readOnly__heartbeatCtx.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiLog

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

/-- (internal) `nil` with nothing queued, else the last position, little-endian, in a fresh slice. -/
def readOnly.heartbeatCtx.spec : Prop :=
  ∀ (ro : Loc) (rs : ReadOnlyState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ readOnly ro rs }}
    (App (Val (ro @!! go.GoType.PointerType go_etcd_io.raft.v3.readOnly.ty @!! go!"heartbeatCtx")) (Val #()))
  {{ (sl : GoSlice), RET #sl; readOnly ro rs ∗
      sl ↦* (if rs.pending = [] then [] else u64Le (W64 rs.position)) }}

end spec
end Raft
end EtcdGrove
end Perennial

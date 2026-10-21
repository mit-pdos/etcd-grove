/-
`(*raft).sendHeartbeatToWitness` (raft#168, `raft.go`; 2026-10-20, witness support).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- The heartbeat `sendHeartbeatToWitness` queues: from `id` to `to` at the term `tm`, with the
context `cl`. Its protocol reading (`wAbs`) is a plain heartbeat with commit `0`. -/
def whbMsg [FfiSyntax] (id to tm : w64) (cl : List w8) : WMsg :=
  ⟨MsgHeartbeat, id, to, tm, W64 0, W64 0, W64 0, [], [], ∅, cl⟩

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `r.sendHeartbeatToWitness(to, ctx)` at a configuration with a witness: the heartbeat
`whbMsg` queued on `r.witnessMsgs`, its reading on the outbox. -/
abbrev raft.sendHeartbeatToWitness.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState) (to : w64) (ctx : GoSlice) (cl : List w8),
  c.wit ≠ W64 0 →
  -- (2026-10-20, W4) to the configuration's witness (what the queue records, `WqOk`)
  to = c.wit →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
      ctx ↦*□ cl }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"sendHeartbeatToWitness"))
      (Val #to)) (Val #ctx))
  {{ RET #(); ownRaftPhysCV c c.voters r id (sendMsgs s [wAbs (whbMsg id to s.term cl)]) }}

end spec

end EtcdGrove
end Perennial

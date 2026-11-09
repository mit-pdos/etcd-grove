/-
## `raft.bcastHeartbeat` (internal)

**Users.** `stepLeader`, `becomeLeader`, `switchToConfig`, `tickHeartbeat` (via `MsgBeat`), each
other. **Proof sketch.** `bcastHeartbeatWithCtx(readOnly.heartbeatCtx())` (R3: the last pending read's context, registered): heartbeats with the commit known matched by each peer. **Changes** (from `specs-ref`'s `raft__bcastHeartbeat.lean`, if any): over
`raftCore`. **Margin.** The messages are inside the token until a `Ready` hands them out.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

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

/-- (internal) A leader sends heartbeats to every other peer. -/
def raft.bcastHeartbeat.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) ,
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ ⌜ρ.role = StateLeader⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"bcastHeartbeat")) (Val #()))
  {{ RET #(); raftCore r γ id ρ }}

end spec
end Raft
end EtcdGrove
end Perennial

/-
## `raft.bcastHeartbeatWithCtx(ctx)` (internal)

**Users.** `bcastHeartbeat` (`raft.go:725`). **Proof sketch.** R4's `Visit`; `sendHeartbeat` to
every peer but itself. **Changes** (from `specs-ref`'s `raft__bcastHeartbeatWithCtx.lean`): over
the opened struct. **Margin.** None on the view.
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

/-- (internal) A leader sends heartbeats with the read-only queue's context to every other peer. -/
def raft.bcastHeartbeatWithCtx.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (ctx : GoSlice) (c : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ coreInv r γ id o ∗ ownSlice ctx c DFrac.discard ∗
      ⌜o.view.role = StateLeader ∧ c = hbCtxOf o.ro⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"bcastHeartbeatWithCtx")) (Val #ctx))
  {{ RET #(); raftOpen r γ id o ∗ coreInv r γ id o }}

end spec
end Raft
end EtcdGrove
end Perennial

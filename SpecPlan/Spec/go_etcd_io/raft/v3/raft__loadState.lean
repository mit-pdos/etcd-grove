/-
## `raft.loadState(state)` (internal)

**Users.** `newRaft` (`raft.go:482`, before the invariant is first established). **Proof sketch.**
Mirrors the code: the commit within `[committed, lastIndex]` (Go panics otherwise, `raft.go:2039`:
`newRaft`'s `StorageHolds`), then `committed`, `Term`, `Vote` set. **Changes** (from `specs-ref`'s
`raft__loadState.lean`): over the opened struct. **Margin.** Exact.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiCore

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

/-- (internal) Loads a stored hard state into a fresh struct. -/
def raft.loadState.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (p : Loc) (dq : DFrac) (hs : HardState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ hardStatePts p dq hs ∗
      ⌜o.log.committed ≤ uint.nat hs.commit ∧ uint.nat hs.commit ≤ o.log.lastIndex⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"loadState")) (Val #p))
  {{ RET #(); hardStatePts p dq hs ∗
      raftOpen r γ id { o with view.hs := hs, log.committed := uint.nat hs.commit } }}

end spec
end Raft
end EtcdGrove
end Perennial

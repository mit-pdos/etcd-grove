/-
## `raft.appendEntry(es...)` (internal)

**Users.** `stepLeader` (`MsgProp`), `becomeLeader` (the empty entry of the term).

**Proof sketch.** Clones the entries at the leader's term and the next indices; `increaseUncommittedSize`
may refuse (the updates dropped); else R3's `append` -- the leader's log of its term grows, the
client updates deposited with their entries (`propUpd`), raft's own entries with none -- and the
leader's own acknowledgement queued after the append (its `msgSent` once durable).

**Changes** (from `specs-ref`'s `raft__appendEntry.lean`): over `raftCore` and the client updates
(was `propsOwn`'s deposit over `NState`). **Margin.** Refusal is silent but for the result.
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

/-- (internal) A leader appends entries at its term, depositing their updates, or refuses them. -/
def raft.appendEntry.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (sl : GoSlice) (dq : DFrac)
    (es : List LogEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ entryPtrs sl dq es ∗
      ([∗list] e ∈ es, ⌜e.isFiller ∨ e.isEmptyV2⌝ ∨ propUpd γ e) ∗ ⌜ρ.role = StateLeader⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"appendEntry")) (Val #sl))
  {{ (acc : Bool), RET #acc; raftCore r γ id ρ ∗ entryPtrs sl dq es }}

end spec
end Raft
end EtcdGrove
end Perennial

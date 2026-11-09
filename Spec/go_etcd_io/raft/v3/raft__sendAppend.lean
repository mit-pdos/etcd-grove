/-
## `raft.sendAppend` (internal)

**Users.** `stepLeader`, `becomeLeader`, `switchToConfig`, `tickHeartbeat` (via `MsgBeat`), each
other. **Proof sketch.** `maybeSendAppend(to, true)`. **Changes** (from `specs-ref`'s `raft__sendAppend.lean`, if any): over
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

/-- (internal) A leader sends an append (or a snapshot) to peer `to`. -/
def raft.sendAppend.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (to : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ ⌜ρ.role = StateLeader ∧ to ≠ id ∧ (ρ.prs !! to).isSome⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"sendAppend")) (Val #to))
  {{ RET #(); raftCore r γ id ρ }}

end spec
end Raft
end EtcdGrove
end Perennial

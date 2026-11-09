/-
## `raft.sendTimeoutNow` (internal)

**Users.** `stepLeader` (`raft.go:1590`, `:1677`). **Proof sketch.** Opens the struct; `send.spec` of a `MsgTimeoutNow` (its `msgJust`: from the leader of the term); closes. **Changes** (from `specs-ref`'s `raft__sendTimeoutNow.lean`, if any): over
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

/-- (internal) A leader tells `to` to campaign at once. -/
def raft.sendTimeoutNow.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (ρ : CoreView) (to : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftCore r γ id ρ ∗ ⌜ρ.role = StateLeader ∧ to ≠ id⌝ }}
    (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"sendTimeoutNow")) (Val #to))
  {{ RET #(); raftCore r γ id ρ }}

end spec
end Raft
end EtcdGrove
end Perennial

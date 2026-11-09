/-
## `JointConfig.IDs()`

**Users.** `ProgressTracker.VoterNodes` (`tracker.go:200`); raft's `campaign` (`raft.go:1063`, the
voters to ask) and `switchToConfig` (`raft.go:2031`, whether the transfer target is still a
voter): R2.

**Proof sketch.** A fresh map; two `range`s inserting each half's ids.

**Changes** (from `specs-ref`'s `quorum/JointConfig__IDs.lean`): over `jointConfigOwn`.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.raft.v3.quorum.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Quorum

open Iris Iris.BI
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.quorum.Assumptions]

/-- Both halves' voters, in a fresh map. -/
def JointConfig.IDs.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (c : go_etcd_io.raft.v3.quorum.JointConfig) (dq : DFrac)
    (s0 s1 : GSet w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗ p ↦{dqp} c ∗ jointConfigOwn c dq s0 s1 }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.quorum.JointConfig.ty @!! go!"IDs")) (Val #()))
  {{ (ids : GoMap), RET #ids; p ↦{dqp} c ∗ jointConfigOwn c dq s0 s1 ∗
      ownMap ids (DFrac.own 1) (s0 ∪ s1) }}

end spec
end Quorum
end EtcdGrove
end Perennial

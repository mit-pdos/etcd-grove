/-
## `assertConfStatesEquivalent(l, cs1, cs2)` (internal)

**Users**: `newRaft` (`raft.go:479`), `appliedSnap` (`raft.go:787`): the restored configuration
against the one switched to. Panics (through `l.Panic`) when they differ: the premise. **Proof
sketch**: `ConfState.Equivalent` (raftpb's `ConfState.Equivalent.spec`: `nil` exactly for `ConfState.Equiv`).
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/assertConfStatesEquivalent.lean`: over raftpb's `confStatePts`.
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

/-- (internal) Returns when the two configurations are equivalent. -/
def assertConfStatesEquivalent.spec : Prop :=
  ∀ (lg : GoInterface) (p1 p2 : Loc) (dq1 dq2 : DFrac) (c1 c2 : ConfState),
  ConfState.Equiv c1 c2 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ confStatePts p1 dq1 c1 ∗ confStatePts p2 dq2 c2 }}
    (App (App (App (Val (@! go_etcd_io.raft.v3.assertConfStatesEquivalent)) (Val #lg)) (Val #p1)) (Val #p2))
  {{ RET #(); confStatePts p1 dq1 c1 ∗ confStatePts p2 dq2 c2 }}

end spec
end Raft
end EtcdGrove
end Perennial

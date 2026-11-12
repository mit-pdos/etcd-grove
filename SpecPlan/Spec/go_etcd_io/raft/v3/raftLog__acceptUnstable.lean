/-
## `(*raftLog).acceptUnstable()` (internal)

**Users**: `acceptReady` (`rawnode.go:430`), once per `Ready`, after the previous batch was absorbed
(R1's `Advance`). Snippet `raftlog/ready.go` (`ReqReadyCycle`).

**Proof sketch**: `unstable.acceptInProgress`; the ghost variable of the batch handed out is set to
`ls.handout` (its other half, `logPending`, to the caller).

**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__acceptUnstable.lean`: the batch is a token (was the field
`unpersisted` and the storage's pending batch `pend`).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiLog

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

/-- (internal) Mark the unstable entries and snapshot as in progress, handing out the batch to write. -/
def raftLog.acceptUnstable.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  ls.handing = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"acceptUnstable")) (Val #()))
  {{ RET #(); raftLog l ls.acceptUnstable ∗
      logPending l ls.handout ls.handout.snap.isSome true }}

end spec
end Raft
end EtcdGrove
end Perennial

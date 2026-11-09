/-
## `newLogWithSize(storage, logger, maxApplyingEntsSize)` (internal)

**Users**: `newRaft` (`raft.go:443`, with `c.MaxCommittedSizePerReady`, non-zero after
`validate`: `ConfigOk`). Snippet `raftlog/append.go` (`ReqStart`).

**Proof sketch**: `FirstIndex`, `LastIndex` through `isStorage`'s atomic triples, their updates
fired on the `S σ` the caller holds (no error: the contract's). The struct is allocated with
`LogState.init σ mx`'s fields; the ghost authority of `ls`'s ghost fields and `logStarting`'s token
are allocated, `S σ` goes into `raftLog` (the starting mode). `Wf`: `stored = σ.ents`, `stable =
σ.last`, `committed = applied = σ.off`, `σ.last + 1 < 2^64`; the budget unpaused with `0 < mx`.

**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/newLogWithSize.lean`: over R1's `isStorage` (was the start bundle's
`FirstIndex`/`LastIndex` triples over a resource `R`, `StorNames`); the storage held by the log
from the start (starting mode) rather than returned. `σ.off ≤ σ.snap.index` (R1's `StorageHolds`)
is new: the log's `logCompactedLb` facts point at the stored snapshot from the start.

**Margin**: none.
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

/-- (internal) A log over storage `st` holding `σ`, in its starting mode. -/
def newLogWithSize.spec : Prop :=
  ∀ (st : GoInterface) (S : StorState → IProp GF) (cf : StorState → ConfState) (σ : StorState)
    (lg : GoInterface) (mx : w64),
  mx ≠ W64 0 → σ.last + 1 < 2 ^ 64 → σ.off ≤ uint.nat σ.snap.index →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isStorage st S cf ∗ S σ ∗ loggerOk lg }}
    (App (App (App (Val (@! go_etcd_io.raft.v3.newLogWithSize)) (Val #st)) (Val #lg)) (Val #mx))
  {{ (l : Loc), RET #l; raftLog l (LogState.init σ mx) ∗ logStarting l S σ }}

end spec
end Raft
end EtcdGrove
end Perennial

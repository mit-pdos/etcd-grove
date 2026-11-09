/-
## `MajorityConfig.CommittedIndex(l)`

**Users.** `JointConfig.CommittedIndex` (each half; `joint.go:50`). Snippet `raftconf/quorum.go`
(`ReqJointCommitted`, through the joint config).

**Proof sketch.** `n := len(c)` (`wp_map_len_lt`: `n < 2^63`); `n = 0`: `MaxUint64`. Else the
`[7]uint64` stack array or `make([]uint64, n)`; the `range` over `c` (`wp_map_for_range`, read only)
calls `l.AckedIndex(id)` through the contract (`isAckedIndexer`, `P` threaded), filling from the
right the found indices (zeros left of them); `slices.Sort` (Perennial's, `n ≤ 2^62`); the element
at `n - (n/2 + 1)` is the largest index a strict majority reached (`MajorityIdx`: the `n/2 + 1`
largest values are at or above it, and above it there are at most `n/2`).

**Changes** (from `specs-ref`'s `quorum/MajorityConfig__CommittedIndex.lean`): the half through
`majorityOwn` (was `ownIdsetQ`-like inline disjunction), the result as `MajorityIdx` (was `MajIdx`/
`IsQuorumIndex`); the size bound named (`sortMax`).

**Margin.** None: `MajorityIdx` determines `N`.
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

/-- The largest index a strict majority of the voters `s` acknowledged (by `l`; an unknown voter
counts `0`); `2^64 - 1` with no voter. -/
def MajorityConfig.CommittedIndex.spec : Prop :=
  ∀ (p : Loc) (dqp : DFrac) (m : GoMap) (dq : DFrac) (s : GSet w64) (l : GoInterface)
    (P : IProp GF) (acked : w64 → Option w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗ p ↦{dqp} m ∗ majorityOwn m dq s ∗ isAckedIndexer l P acked ∗ P ∗
      ⌜GMap.size s ≤ sortMax⌝ }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.raft.v3.quorum.MajorityConfig.ty @!! go!"CommittedIndex")) (Val #l))
  {{ (N : w64), RET #N; p ↦{dqp} m ∗ majorityOwn m dq s ∗ P ∗
      ⌜MajorityIdx s (fun v => (acked v).getD (W64 0)) N⌝ }}

end spec
end Quorum
end EtcdGrove
end Perennial

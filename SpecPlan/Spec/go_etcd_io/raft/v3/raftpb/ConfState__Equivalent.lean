/-
`(*ConfState).Equivalent(cs2)` (`raftpb/confstate.go:26`).

Users: raft's `assertConfStatesEquivalent` (`util.go:321`, R3: `newRaft` and `appliedSnap` check the
tracker's `ConfState` against the storage's), etcd's server tests. Snippet:
`examples/specreq/raftpb/confchange.go` (`ReqEquivalent`).

Proof sketch: neither is `nil` (`raftpb_ne_null`). `proto.Clone` of each (2a's `Clone.spec` through
`confStatePts_msgAt`: fresh `msgAt ConfState.ty q (own 1) c` with `confStateIs c cs false`, so
`confStatePts q (own 1) cs`); for each clone, `confStatePts_unfold`, `slices.Sort` of the four
slices in place (Perennial's spec: a sorted permutation; `cs.lenOk` gives its length bound),
`GetAutoLeave()` and a fresh cell for it (now set): `confStateFull q (own 1) cs'` with `cs'` the
sorted lists and the same `AutoLeave`; `confStateFull_msgAt` gives contents `c1`, `c2` with
`confStateIs ci csi' true`; `proto.Equal` (2a) answers `norm c1 = norm c2` (the converse by
`noFloats_raftpb`), which by `confState_ext` one way and `raftpb_norm` with the readers being
functions the other is `cs1' = cs2'`, i.e. (sorted permutations under a total order) `cs1.Equiv
cs2`. On a mismatch, `fmt.Errorf` of the four `*ConfState`s under `%+#v`: Perennial's `fmt.Errorf`
admits no pointer argument, so this step is raftpb's assumed `fmtErrorf.spec` (`FmtErrorf.lean`,
four `FmtArg.confState` arguments: the two clones at `own 1`, the inputs at `dq1`, `dq2`, all
given back): a non-nil error.

Changes: from `specs-ref/.../raftpb/ConfState__Equivalent.lean`: both outcomes specified (the old
spec gave only the `nil` one, under `Perm`); the `proto.Equal` step goes through protobuf's content
(`confState_ext`) instead of the old `EqualConfState` over the refuted `pbEnc`; the length bound is
part of the predicate (`ConfState.lenOk`).

Changes: verify-round: (A5-provability F3) the mismatch path's `fmt.Errorf` is now on an assumed
boundary spec (`fmtErrorf.spec`) instead of Perennial's, which does not cover it; the triple is
unchanged. verify-round (second pass): the `Equal` step goes through 2a's `norm` (`confState_ext`
restated up to `norm`, `raftpb_norm`, `noFloats_raftpb`).

Margin: two `nil` inputs (an error) are not specified (no user).
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.raftpb.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace RaftPb

open Iris Iris.BI
open go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-- `p.Equivalent(q)`: `nil` exactly when the two `ConfState`s list the same configuration. -/
def ConfState.Equivalent.spec : Prop :=
  ∀ (p q : Loc) (dq1 dq2 : DFrac) (cs1 cs2 : ConfState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ confStatePts p dq1 cs1 ∗ confStatePts q dq2 cs2 }}
    (App (Val (p @!! go.GoType.PointerType raftpb.ConfState.ty @!! go!"Equivalent")) (Val #q))
  {{ (err : GoInterface), RET #err; confStatePts p dq1 cs1 ∗ confStatePts q dq2 cs2 ∗
      ⌜err = GoInterface.nil ↔ cs1.Equiv cs2⌝ }}

end spec

end RaftPb
end EtcdGrove
end Perennial

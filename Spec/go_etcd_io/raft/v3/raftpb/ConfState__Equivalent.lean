/-
Port of election_proof/spec_ConfState__Equivalent.v (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `cs1.Equivalent(cs2)` (`raftpb/confstate.go`) returns `nil` iff the two
`ConfState`s are `reflect.DeepEqual` after each of their four id slices has been copied
with `append([]uint64(nil), s...)` and sorted.

**Not translated** (`raftpb` is types-only), so this is an `axiom`. It is stated for the
voters-only case `newRaft` needs: both sides have empty `VotersOutgoing`, `Learners`
and `LearnersNext`, equal `AutoLeave`, and `Voters` lists that are permutations of each
other. Then every slice sorts to the same list -- the empty ones to `nil`, whether they
started `nil` or empty, because `append` of nothing to `nil` is `nil` -- and
`ConfState` has exactly these five fields (`raftpb/raft.pb.go`), so `DeepEqual` holds
and the result is `nil`. The `Voters` lists have at most `2^62` elements, the bound of
`slices.Sort` (which `Equivalent` calls).

Only the `nil` outcome is specified: the one caller, `assertConfStatesEquivalent`,
`Panic`s on anything else. -/
abbrev raftpb.ConfState.Equivalent.spec : Prop :=
  ∀ (p : Loc) (cs1 cs2 : raftpb.ConfState) (v1 v2 : List w64) (dq1 dq2 : DFrac),
  v1 ≡ₚ v2 → (v1.length : Int) ≤ 2 ^ 62 →
  cs1.VotersOutgoing'.len = W64 0 →
  cs1.Learners'.len = W64 0 →
  cs1.LearnersNext'.len = W64 0 →
  cs2.VotersOutgoing'.len = W64 0 →
  cs2.Learners'.len = W64 0 →
  cs2.LearnersNext'.len = W64 0 →
  cs1.AutoLeave' = cs2.AutoLeave' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ p ↦ cs1 ∗
      cs1.Voters' ↦*{dq1} v1 ∗
      cs2.Voters' ↦*{dq2} v2 }}
    (App (Val (p @!! go.GoType.PointerType raftpb.ConfState.ty @!! go!"Equivalent"))
      (Val #cs2))
  {{ RET #interface.nil;
      p ↦ cs1 ∗
      cs1.Voters' ↦*{dq1} v1 ∗
      cs2.Voters' ↦*{dq2} v2 }}

end spec

end EtcdGrove
end Perennial

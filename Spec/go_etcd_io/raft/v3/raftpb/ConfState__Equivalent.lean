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

For **any** two `ConfState`s (2026-10-14, reconfiguration stage B8; until then the non-joint
case only, now `specS`): equal `AutoLeave`, and each of the four id lists of one a permutation
of the other's (`CSLists.Perm`). Then every slice sorts to the same list -- the empty ones to
`nil`, whether they started `nil` or empty, because `append` of nothing to `nil` is `nil` --
and `ConfState` has exactly these five fields (`raftpb/raft.pb.go`), so `DeepEqual` holds and
the result is `nil`. Each list has at most `2^62` elements, the bound of `slices.Sort` (which
`Equivalent` calls). `Voters` is a points-to; the other three may be `nil` with no points-to
when empty (`ownIdList`, in `ownCSIds`).

Only the `nil` outcome is specified: the one caller, `assertConfStatesEquivalent`,
`Panic`s on anything else. -/
abbrev raftpb.ConfState.Equivalent.spec : Prop :=
  ∀ (p : Loc) (cs1 cs2 : raftpb.ConfState) (a b : CSLists) (dq1 dq2 dl1 dl2 : DFrac),
  a.Perm b → a.Bounded →
  cs1.AutoLeave' = cs2.AutoLeave' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ p ↦ cs1 ∗
      ownCSIds cs1 dq1 dl1 a ∗ ownCSIds cs2 dq2 dl2 b }}
    (App (Val (p @!! go.GoType.PointerType raftpb.ConfState.ty @!! go!"Equivalent"))
      (Val #cs2))
  {{ RET #interface.nil;
      p ↦ cs1 ∗ ownCSIds cs1 dq1 dl1 a ∗ ownCSIds cs2 dq2 dl2 b }}

/-- The statement until 2026-10-14: the non-joint case (both sides with empty
`VotersOutgoing` and `LearnersNext`). Derived by `spec_simple`. -/
abbrev raftpb.ConfState.Equivalent.specS : Prop :=
  ∀ (p : Loc) (cs1 cs2 : raftpb.ConfState) (v1 v2 l1 l2 : List w64) (dq1 dq2 dl1 dl2 : DFrac),
  v1 ≡ₚ v2 → (v1.length : Int) ≤ 2 ^ 62 →
  l1 ≡ₚ l2 → (l1.length : Int) ≤ 2 ^ 62 →
  cs1.VotersOutgoing'.len = W64 0 →
  cs1.LearnersNext'.len = W64 0 →
  cs2.VotersOutgoing'.len = W64 0 →
  cs2.LearnersNext'.len = W64 0 →
  cs1.AutoLeave' = cs2.AutoLeave' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗ p ↦ cs1 ∗
      cs1.Voters' ↦*{dq1} v1 ∗
      cs2.Voters' ↦*{dq2} v2 ∗
      ownIdList cs1.Learners' dl1 l1 ∗
      ownIdList cs2.Learners' dl2 l2 }}
    (App (Val (p @!! go.GoType.PointerType raftpb.ConfState.ty @!! go!"Equivalent"))
      (Val #cs2))
  {{ RET #interface.nil;
      p ↦ cs1 ∗
      cs1.Voters' ↦*{dq1} v1 ∗
      cs2.Voters' ↦*{dq2} v2 ∗
      ownIdList cs1.Learners' dl1 l1 ∗
      ownIdList cs2.Learners' dl2 l2 }}

open Iris.ProofMode in
theorem raftpb.ConfState.Equivalent.spec_simple
    (H : raftpb.ConfState.Equivalent.spec (GF := GF) (hG := hG)) :
    raftpb.ConfState.Equivalent.specS (GF := GF) (hG := hG) := by
  intro p cs1 cs2 v1 v2 l1 l2 dq1 dq2 dl1 dl2 Hperm Hlen Hlperm Hllen H1 H3 H4 H6 Hal
  iintro %Φ ⟨#Hpkg, Hp, Hv1, Hv2, Hl1, Hl2⟩ HΦ
  ihave Hc1 : ownCSIds (GF := GF) cs1 dq1 dl1 ⟨v1, l1, [], []⟩ $$ [Hv1 Hl1]
  · unfold ownCSIds ownIdList
    iframe Hv1 Hl1
    isplitr
    · ileft; ipureintro; exact ⟨H1, rfl⟩
    ileft; ipureintro; exact ⟨H3, rfl⟩
  ihave Hc2 : ownCSIds (GF := GF) cs2 dq2 dl2 ⟨v2, l2, [], []⟩ $$ [Hv2 Hl2]
  · unfold ownCSIds ownIdList
    iframe Hv2 Hl2
    isplitr
    · ileft; ipureintro; exact ⟨H4, rfl⟩
    ileft; ipureintro; exact ⟨H6, rfl⟩
  iapply H p cs1 cs2 ⟨v1, l1, [], []⟩ ⟨v2, l2, [], []⟩ dq1 dq2 dl1 dl2
    ⟨Hperm, Hlperm, List.Perm.refl _, List.Perm.refl _⟩
    ⟨Hlen, Hllen, by simp, by simp⟩ Hal $$ [$Hpkg $Hp $Hc1 $Hc2]
  inext
  iintro ⟨Hp, Hc1, Hc2⟩
  unfold ownCSIds
  icases Hc1 with ⟨Hv1, Hl1, -, -⟩
  icases Hc2 with ⟨Hv2, Hl2, -, -⟩
  iapply HΦ
  iframe

end spec

end EtcdGrove
end Perennial

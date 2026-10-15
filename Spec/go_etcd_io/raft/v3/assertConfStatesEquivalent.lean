/- Port of election_proof/spec_assertConfStatesEquivalent.v (feb5c73d4). -/
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

/-- `assertConfStatesEquivalent l cs1 cs2` returns iff `cs1.Equivalent(cs2)` is `nil`,
and otherwise calls `l.Panic`. Stated for the case `ConfState.Equivalent`'s triple covers
(`Spec/ConfState__Equivalent.lean`): since 2026-10-14 (reconfiguration stage B8) any two
`ConfState`s with equal `AutoLeave` and each id list a permutation of the other's, joint ones
included (until then the non-joint case, now `specS`); the `Panic` path is then unreachable,
which is why the logger needs no contract here. -/
abbrev assertConfStatesEquivalent.spec : Prop :=
  ∀ (l : Logger) (cs1 cs2 : raftpb.ConfState) (a b : CSLists) (dq1 dq2 dl1 dl2 : DFrac),
  a.Perm b → a.Bounded →
  cs1.AutoLeave' = cs2.AutoLeave' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      ownCSIds cs1 dq1 dl1 a ∗ ownCSIds cs2 dq2 dl2 b }}
    (App (App (App (Val #(functions assertConfStatesEquivalent [])) (Val #l))
      (Val #cs1)) (Val #cs2))
  {{ RET #(); ownCSIds cs1 dq1 dl1 a ∗ ownCSIds cs2 dq2 dl2 b }}

/-- The statement until 2026-10-14 (the non-joint case). Derived by `spec_simple`. -/
abbrev assertConfStatesEquivalent.specS : Prop :=
  ∀ (l : Logger) (cs1 cs2 : raftpb.ConfState) (v1 v2 l1 l2 : List w64) (dq1 dq2 dl1 dl2 : DFrac),
  v1 ≡ₚ v2 → (v1.length : Int) ≤ 2 ^ 62 →
  l1 ≡ₚ l2 → (l1.length : Int) ≤ 2 ^ 62 →
  cs1.VotersOutgoing'.len = W64 0 →
  cs1.LearnersNext'.len = W64 0 →
  cs2.VotersOutgoing'.len = W64 0 →
  cs2.LearnersNext'.len = W64 0 →
  cs1.AutoLeave' = cs2.AutoLeave' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      cs1.Voters' ↦*{dq1} v1 ∗
      cs2.Voters' ↦*{dq2} v2 ∗
      ownIdList cs1.Learners' dl1 l1 ∗
      ownIdList cs2.Learners' dl2 l2 }}
    (App (App (App (Val #(functions assertConfStatesEquivalent [])) (Val #l))
      (Val #cs1)) (Val #cs2))
  {{ RET #();
      cs1.Voters' ↦*{dq1} v1 ∗
      cs2.Voters' ↦*{dq2} v2 ∗
      ownIdList cs1.Learners' dl1 l1 ∗
      ownIdList cs2.Learners' dl2 l2 }}

open Iris.ProofMode in
theorem assertConfStatesEquivalent.spec_simple
    (H : assertConfStatesEquivalent.spec (GF := GF) (hG := hG)) :
    assertConfStatesEquivalent.specS (GF := GF) (hG := hG) := by
  intro l cs1 cs2 v1 v2 l1 l2 dq1 dq2 dl1 dl2 Hperm Hlen Hlperm Hllen H1 H3 H4 H6 Hal
  iintro %Φ ⟨#Hpkg, Hv1, Hv2, Hl1, Hl2⟩ HΦ
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
  iapply H l cs1 cs2 ⟨v1, l1, [], []⟩ ⟨v2, l2, [], []⟩ dq1 dq2 dl1 dl2
    ⟨Hperm, Hlperm, List.Perm.refl _, List.Perm.refl _⟩
    ⟨Hlen, Hllen, by simp, by simp⟩ Hal $$ [$Hpkg $Hc1 $Hc2]
  inext
  iintro ⟨Hc1, Hc2⟩
  unfold ownCSIds
  icases Hc1 with ⟨Hv1, Hl1, -, -⟩
  icases Hc2 with ⟨Hv2, Hl2, -, -⟩
  iapply HΦ
  iframe

end spec

end EtcdGrove
end Perennial

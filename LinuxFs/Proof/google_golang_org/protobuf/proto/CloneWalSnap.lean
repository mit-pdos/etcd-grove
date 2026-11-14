/-
The proof of `LinuxFs/Spec/google_golang_org/protobuf/proto/CloneWalSnap.lean`: `proto.Clone` of a
frozen `*walpb.Snapshot`, over `proto.ClonePb.spec` (the main tree's per-type trust boundary, the
part's generated copy of its spec) at the registered `pbSnapC` (`pbSnapC_reg`): the clone is
`snapOwnC` at a content of the same model (`eqv` is equality there), which `snapOwnC_freeze` freezes
(the hidden fields of both levels into the protobuf invariant). (2026-11-14.)

The part has no copy of `ClonePb`'s axiom (`proto.ClonePb.wp_proof`) yet: linking this proof needs it
(`etc/gen-part-copies.py`, as `MarshalPb`'s).
-/
module

public import LinuxFs.Spec.google_golang_org.protobuf.proto.CloneWalSnap
public import LinuxFs.Spec.google_golang_org.protobuf.proto.ClonePb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.storage.wal go_etcd_io.raft.v3 WalEnc

section freeze
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A decoded conf state pointer, frozen** (its hidden fields into the protobuf invariant). -/
theorem walCsOwnC_freeze (p : Loc) (o : Option WalCsC) :
    walCsOwnC (GF := GF) p o ⊢ |={⊤}=> walCsOptRoC p o := by
  cases o with
  | none =>
    unfold walCsOwnC walCsOptRoC
    iintro H; imodintro; iexact H
  | some c =>
    unfold walCsOwnC walCsOptRoC walCsRoC walCsHidden
    iintro ⟨%v, Hl, Hv, Hle, Hvo, Hln, #Ha, Huf, %Hu⟩
    ihave ⟨Hl, %Hn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hl
    iStructNamed Hl
    ipersist Voters
    ipersist Learners
    ipersist VotersOutgoing
    ipersist LearnersNext
    ipersist AutoLeave
    ipersist Hv
    ipersist Hle
    ipersist Hvo
    ipersist Hln
    imod inv_alloc (nroot.@"protobuf") ⊤ (iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
        (sc : w32) (us : GoSlice),
      p.[raftpb.ConfState, go!"state"] ↦ st ∗ p.[raftpb.ConfState, go!"sizeCache"] ↦ sc ∗
        p.[raftpb.ConfState, go!"unknownFields"] ↦ us ∗ us ↦* c.uf)) $$ [state sizeCache unknownFields Huf]
      with #Hinv
    · inext
      iexists v.state', v.sizeCache', v.unknownFields'
      iframe
    imodintro
    iexists v.Voters', v.Learners', v.VotersOutgoing', v.LearnersNext', v.AutoLeave'
    isplitr
    · ipureintro; exact Hn
    iframe #
    ipureintro; exact Hu

/-- **A decoded `*walpb.Snapshot`, frozen** (`snapOwnC` to `snapRoC`: the field cells already
persistent, the conf state frozen, both levels' hidden fields into the protobuf invariant). -/
theorem snapOwnC_freeze (l : Loc) (c : WalSnapC) :
    snapOwnC (GF := GF) l c ⊢ |={⊤}=> snapRoC l c := by
  unfold snapOwnC snapRoC
  iintro ⟨%v, Hl, #Hi, #Ht, Hc, Huf, %Hu⟩
  ihave ⟨Hl, %Hn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hl
  iStructNamed Hl
  ipersist Index
  ipersist Term
  ipersist ConfState
  imod walCsOwnC_freeze v.ConfState' c.confState $$ Hc with #Hc
  imod inv_alloc (nroot.@"protobuf") ⊤ (iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
      (sc : w32) (us : GoSlice),
    l.[walpb.Snapshot, go!"state"] ↦ st ∗ l.[walpb.Snapshot, go!"sizeCache"] ↦ sc ∗
      l.[walpb.Snapshot, go!"unknownFields"] ↦ us ∗ us ↦* c.uf)) $$ [state sizeCache unknownFields Huf]
    with #Hinv
  · inext
    iexists v.state', v.sizeCache', v.unknownFields'
    iframe
  imodintro
  iexists v.Index', v.Term', v.ConfState'
  isplitr
  · ipureintro; exact Hn
  unfold snapHidden
  isplitl []
  · iexact Index
  isplitl []
  · iexact Hi
  isplitl []
  · iexact Term
  isplitl []
  · iexact Ht
  isplitl []
  · iexact ConfState
  isplitl []
  · iexact Hc
  isplitl []
  · iexact Hinv
  ipureintro; exact Hu

end freeze

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem proto.CloneWalSnap.wp_proof (wp_Clone : proto.ClonePb.spec (GF := GF) (hG := hG)) :
    proto.CloneWalSnap.spec (GF := GF) (hG := hG) := by
  intro sp s
  unfold walSnapIdTerm
  iintro %Φ ⟨#Hpkg, Hpre⟩ HΦ
  icases Hpre with ⟨%c, Hro, %hs⟩
  have hC := wp_Clone pbSnapC pbSnapC_reg sp c
  simp only [pbSnapC_ty, pbSnapC_roC] at hC
  iapply wp_fupd
  wp_apply hC $$ [Hro] as %l' ⟨%c', Hd, %Hp⟩
  · iframe
  obtain ⟨heqv, -, -⟩ := Hp
  imod snapOwnC_freeze l' c' $$ Hd with Hd
  imodintro
  iapply HΦ
  iexists c'
  iframe
  ipureintro
  rw [← hs]
  exact (congrArg (fun m => (SnapshotMetadataM.Index' m, SnapshotMetadataM.Term' m)) heqv).symm

end proof

end EtcdGrove
end Perennial

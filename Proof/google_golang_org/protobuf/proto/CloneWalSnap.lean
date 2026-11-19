/-
The proof of `Spec/google_golang_org/protobuf/proto/CloneWalSnap.lean`: `proto.Clone` of a
frozen `*walpb.Snapshot`, over `proto.ClonePb.spec` (the main tree's per-type trust boundary, the
part's generated copy of its spec) at the registered `pbSnapC` (`pbSnapC_reg`): the clone is
`snapOwnC` at a content of the same model (`eqv` is equality there), which `snapOwnC_freeze` freezes
(the hidden fields of both levels into the protobuf invariant). (2026-11-14.)

The part has no copy of `ClonePb`'s axiom (`proto.ClonePb.wp_proof`) yet: linking this proof needs it
(`etc/gen-part-copies.py`, as `MarshalPb`'s).
-/
module

public import Spec.google_golang_org.protobuf.proto.CloneWalSnap
public import Spec.google_golang_org.protobuf.proto.ClonePb
public import Proof.google_golang_org.protobuf.proto.CloneWalSnapLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.storage.wal go_etcd_io.raft.v3 WalEnc

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

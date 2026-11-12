/-
Port of `election_proof/proof_unstable__nextSnapshot.v` (857d09190).
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.unstable__nextSnapshot
public import RaftWitness.Spec.google_golang_org.protobuf.proto.CloneSnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- raft v3.7: the pending snapshot is returned as a fresh clone (`log_unstable.go:114`); the
clone is taken of the snapshot `pendKsn` describes, so the record it holds is in `ksn`. -/
theorem unstable.nextSnapshot.wp_proof
    (wp_proto_CloneSnapshot : proto.CloneSnapshot.spec (GF := GF) (hG := hG)) :
    unstable.nextSnapshot.spec (GF := GF) (hG := hG) := by
  intro u us
  wp_start as H
  iNamed H
  open_unstable
  wp_auto
  rcases snap_some_or_none us.snap with ⟨sid, Hs⟩ | Hs
  · ihave Hpk := Hpksn
    iunfold pendKsn at Hpk
    icases Hpk $$ %sid %Hs with ⟨%sv, #Hsv, %Hid, %Hin⟩
    ihave %Hnn : ⌜uv.snapshot' ≠ null⌝ $$ [Hsv]
    · iunfold ownSnapM at Hsv; iNamed Hsv; ipureintro; exact Hnn
    simp only [Hnn, _root_.decide_false]
    wp_auto
    rcases Hsip : uv.snapshotInProgress' <;> wp_auto
    · wp_apply wp_proto_CloneSnapshot.1 _ DFrac.discard sv $$ [$Hsv] as %p' ⟨-, Hc⟩
      iapply HΦ
      isplitl [Hu Hents_cap Hents]
      · close_unstable
      isplitr
      · ipureintro; rw [Hs]; intro h; cases h
      iright
      iexists sid, sv
      iframe Hc
      ipureintro; exact ⟨Hs, Hid, Hin⟩
    · iapply HΦ
      isplitl
      · close_unstable
      isplitr
      · ipureintro; intro _; rfl
      ileft; ipureintro; rfl
  · ihave %Hn := ownSnap_of_eq_none Hs $$ Hsnap
    simp only [decide_eq_true Hn]
    wp_auto
    iapply HΦ
    isplitl
    · close_unstable
    isplitr
    · ipureintro; intro _; rfl
    ileft; ipureintro; rfl

end proof

end EtcdGrove
end Perennial

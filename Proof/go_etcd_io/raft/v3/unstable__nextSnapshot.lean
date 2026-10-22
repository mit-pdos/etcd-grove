/-
Port of `election_proof/proof_unstable__nextSnapshot.v` (857d09190).
-/
module

public import Spec.go_etcd_io.raft.v3.unstable__nextSnapshot
public import Spec.google_golang_org.protobuf.proto.CloneSnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
    · iunfold ownSnapS at Hsv; iNamed Hsv; ipureintro; exact Hnn
    simp only [Hnn, _root_.decide_false]
    wp_auto
    rcases Hsip : us.sip <;> wp_auto
    · wp_apply wp_proto_CloneSnapshot.2.2.2 _ DFrac.discard sv $$ [$Hsv] as %p' ⟨-, Hc⟩
      -- the clone is not `nil`
      iunfold ownSnapS at Hc
      icases Hc with ⟨%ds, %pm, %uf, %Hnn', Hc⟩
      iapply HΦ
      isplitl [Hu Hents_cap Hents]
      · iapply ownUnstable_intro $$ Hu Hents_cap Hents Hsnap Hpksn Hlogger
        ipureintro; exact ⟨rfl, rfl, Hsip.symm⟩
      isplitr
      · ipureintro; rw [Hs]; simp [Hnn']
      iright
      iexists sid, sv
      isplitr
      · ipureintro; exact ⟨Hs, rfl, Hid, Hin⟩
      iunfold ownSnapS
      iexists ds, pm, uf
      isplitr
      · ipureintro; exact Hnn'
      iexact Hc
    · iapply HΦ
      isplitl
      · iapply ownUnstable_intro $$ Hu Hents_cap Hents Hsnap Hpksn Hlogger
        ipureintro; exact ⟨rfl, rfl, Hsip.symm⟩
      isplitr
      · ipureintro; simp
      ileft; ipureintro; rfl
  · ihave %Hn := ownSnap_of_eq_none Hs $$ Hsnap
    simp only [decide_eq_true Hn]
    wp_auto
    iapply HΦ
    isplitl
    · close_unstable
    isplitr
    · ipureintro; simp [Hs]
    ileft; ipureintro; rfl

end proof

end EtcdGrove
end Perennial

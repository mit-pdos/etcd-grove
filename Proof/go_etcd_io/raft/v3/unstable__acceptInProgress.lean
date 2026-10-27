/-
Port of `election_proof/proof_unstable__acceptInProgress.v` (857d09190).
-/
module

public import Spec.go_etcd_io.raft.v3.unstable__acceptInProgress
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex

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

theorem unstable.acceptInProgress.wp_proof
    (wp_Entry_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)) :
    unstable.acceptInProgress.spec (GF := GF) (hG := hG) := by
  intro u us Hidx Hnw
  wp_start as H
  iNamed H
  open_unstable
  icases Hents with #Hents
  ihave %Hlen := entsPts_len $$ Hents
  wp_auto
  by_cases He : us.ents = []
  · -- no entries: only the snapshot flag
    wp_if_destruct
    · exfalso; simp [He] at Hlen; word
    wp_if_destruct
    · -- no snapshot pending
      ihave %Hsn : ⌜us.snap.isSome = false⌝ $$ [Hsnap]
      · rcases snap_some_or_none us.snap with ⟨sid, Hs⟩ | Hs
        · icases ownSnap_of_eq_some Hs $$ Hsnap with ⟨%sv, Hsv, -⟩
          iunfold ownSnapM at Hsv; iNamed Hsv
          exfalso; first | exact Hnn Hif | exact Hif Hn | exact absurd Hif Hnn | exact absurd Hn Hif
        · ipureintro; rw [Hs]; rfl
      iapply HΦ
      isplitl
      · iapply ownUnstable_intro $$ Hu Hents_cap Hents Hsnap Hpksn Hlogger
        ipureintro; refine ⟨rfl, rfl, ?_⟩; simp [Hsn]
      ipureintro
      simp [He]
    · -- a snapshot pending: in progress now
      ihave %Hsn : ⌜us.snap.isSome = true⌝ $$ [Hsnap]
      · rcases snap_some_or_none us.snap with ⟨sid, Hs⟩ | Hs
        · ipureintro; rw [Hs]; rfl
        · ihave %Hn := ownSnap_of_eq_none Hs $$ Hsnap
          exfalso; first | exact Hnn Hif | exact Hif Hn | exact absurd Hif Hnn | exact absurd Hn Hif
      iapply HΦ
      isplitl
      · iapply ownUnstable_intro $$ Hu Hents_cap Hents Hsnap Hpksn Hlogger
        ipureintro; refine ⟨rfl, rfl, ?_⟩; simp [Hsn]
      ipureintro
      simp [He]
  · obtain ⟨es, e, Hes⟩ := List.eq_nil_or_concat us.ents |>.resolve_left He
    have Hl : us.ents.length = es.length + 1 := by simp [Hes]
    have Hle : us.ents[us.ents.length - 1]? = some e := by
      rw [Hes]; simp
    have Heidx := Hidx _ _ Hle
    wp_if_destruct
    rotate_left
    · exfalso; word
    have Hbnd : 0 ≤ sint.Z (uv.entries'.len - W64 1) ∧
        sint.Z (uv.entries'.len - W64 1) < sint.Z uv.entries'.len := by
      constructor <;> word
    rw [ite_eq_left Hbnd]
    have Hk : (sint.Z (uv.entries'.len - W64 1)).toNat = us.ents.length - 1 := by word
    have Hle' : us.ents[(sint.Z (uv.entries'.len - W64 1)).toNat]? = some e := by rw [Hk]; exact Hle
    ihave Hents' := Hents
    iunfold entsRO at Hents'
    iunfold entsPts at Hents'
    icases Hents' with ⟨%ls, #Hls, #Hb⟩
    icases entsBig_lookup ls us.ents _ e Hle' $$ Hb with ⟨%l, %Hl, #Hel⟩
    wp_apply wp_load_slice_index uv.entries' (sint.Z (uv.entries'.len - W64 1)) ls DFrac.discard l
      Hbnd.1 $$ [Hls] as -
    · iframe Hls; ipureintro; exact Hl
    wp_apply wp_Entry_GetIndex.1 l DFrac.discard e $$ [$Hel] as -
    wp_if_destruct
    · -- no snapshot pending
      ihave %Hsn : ⌜us.snap.isSome = false⌝ $$ [Hsnap]
      · rcases snap_some_or_none us.snap with ⟨sid, Hs⟩ | Hs
        · icases ownSnap_of_eq_some Hs $$ Hsnap with ⟨%sv, Hsv, -⟩
          iunfold ownSnapM at Hsv; iNamed Hsv
          exfalso; first | exact Hnn Hif | exact Hif Hn | exact absurd Hif Hnn | exact absurd Hn Hif
        · ipureintro; rw [Hs]; rfl
      iapply HΦ
      isplitl
      · iapply ownUnstable_intro $$ Hu Hents_cap Hents Hsnap Hpksn Hlogger
        ipureintro; refine ⟨rfl, rfl, ?_⟩; simp [Hsn]
      ipureintro
      refine ⟨fun h => absurd h He, fun _ => ?_⟩
      word
    · -- a snapshot pending: in progress now
      ihave %Hsn : ⌜us.snap.isSome = true⌝ $$ [Hsnap]
      · rcases snap_some_or_none us.snap with ⟨sid, Hs⟩ | Hs
        · ipureintro; rw [Hs]; rfl
        · ihave %Hn := ownSnap_of_eq_none Hs $$ Hsnap
          exfalso; first | exact Hnn Hif | exact Hif Hn | exact absurd Hif Hnn | exact absurd Hn Hif
      iapply HΦ
      isplitl
      · iapply ownUnstable_intro $$ Hu Hents_cap Hents Hsnap Hpksn Hlogger
        ipureintro; refine ⟨rfl, rfl, ?_⟩; simp [Hsn]
      ipureintro
      refine ⟨fun h => absurd h He, fun _ => ?_⟩
      word

end proof

end EtcdGrove
end Perennial

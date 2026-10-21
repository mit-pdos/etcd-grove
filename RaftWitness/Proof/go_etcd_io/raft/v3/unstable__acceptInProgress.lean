/-
Port of `election_proof/proof_unstable__acceptInProgress.v` (857d09190).
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.unstable__acceptInProgress
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex

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
    wp_if_destruct <;>
    · iapply HΦ
      isplitl
      · close_unstable
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
    wp_if_destruct <;>
    · iapply HΦ
      isplitl
      · close_unstable
      ipureintro
      refine ⟨fun h => absurd h He, fun _ => ?_⟩
      word

end proof

end EtcdGrove
end Perennial

/-
Port of `election_proof/proof_entsSize.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.entsSize
public import Spec.google_golang_org.protobuf.proto.SizePb
public import Proof.go_etcd_io.raft.v3.PbEntryType
public import Proof.go_etcd_io.raft.v3.limitSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A `for range` accumulating `proto.Size(ent)` into `size`. raft v3.7: the range variable `ent`
is a `*pb.Entry` (allocated outside the loop, so in the invariant). (out_size C3) Weighed by
`proto.SizePb` at `Entry`'s registered instance (at `HasLC.hasLC`); the invariant tracks, when the
entries are sized and their sizes sum below `2^64`, that `size` is the sum over the prefix seen. -/
theorem entsSize.wp_proof
    (wp_SizePb : proto.SizePb.spec (GF := GF) (hG := hG)) :
    entsSize.spec (GF := GF) (hG := hG) := by
  intro sz s cs dq
  wp_start as H
  iNamed H
  iunfold entsPtsC at Hs
  icases Hs with ⟨%ls, Hs, #Hb, %Hz⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hbl := entsBigC_length _ _ $$ Hb
  ihave IH : iprop(∃ (n acc : w64) (ev : Loc),
      "i" ∷ i_ptr ↦ n ∗ "size" ∷ size_ptr ↦ acc ∗ "ent" ∷ ent_ptr ↦ ev ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (cs.length : Int) ∧
        (sz = true → (cs.map entrySize).sum < 2 ^ 64 →
          uint.nat acc = ((cs.take (sint.nat n)).map entrySize).sum)⌝) $$ [i size ent]
  · iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, fun _ _ => ?_⟩
    rw [show sint.nat (W64 0) = 0 from rfl]; simp only [List.take_zero, List.map_nil, List.sum_nil]; rfl
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < cs.length := by word
    obtain ⟨c, Hc⟩ : ∃ c, cs[(sint.Z n).toNat]? = some c :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    icases entsBigC_lookup ls cs _ c Hc $$ Hb with ⟨%l, %Hl, #Hl⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index s (sint.Z n) ls dq l Hn.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hl
    have wpS := wp_SizePb pbEntryC pbEntryC_reg l c
    simp only [pbEntryC_ty, pbEntryC_roC, pbEntryC_size] at wpS
    wp_apply wpS $$ [$Hl] as %ni %Hni
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, fun h1 h2 => ?_⟩
    have hok := Hz h1 c (List.mem_of_getElem? Hc)
    have hlt := entrySize_lt_of_ok c hok
    have Hni' := Hni (by omega)
    have Ha := Hn.2.2 h1 h2
    have hidx : sint.nat (n + W64 1) = (sint.Z n).toNat + 1 := by word
    have Hpre : ((cs.take ((sint.Z n).toNat + 1)).map entrySize).sum ≤ (cs.map entrySize).sum := by
      have h := congrArg List.sum (List.take_append_drop ((sint.Z n).toNat + 1) (cs.map entrySize))
      rw [List.sum_append, ← List.map_take] at h
      rw [← h]; exact Nat.le_add_right _ _
    rw [entrySize_sum_take_succ cs _ c Hc] at Hpre
    rw [hidx, entrySize_sum_take_succ cs _ c Hc]
    have Ha' : uint.nat acc = ((cs.take (sint.Z n).toNat).map entrySize).sum := Ha
    exact w64_add_exact acc ni _ _ Ha' Hni' (by omega) (by omega)
  · iapply HΦ
    have Hle : sint.nat n = cs.length := by word
    isplitl
    · iunfold entsPtsC
      iexists ls
      iframe Hs Hb
      ipureintro; exact Hz
    · ipureintro
      intro h1 h2
      have Ha := Hn.2.2 h1 h2
      rw [Hle, List.take_length] at Ha
      exact Ha

end proof

end EtcdGrove
end Perennial

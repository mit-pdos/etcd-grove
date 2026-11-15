/- Port of election_proof/proof_limitSize.v. -/
module

public import Spec.go_etcd_io.raft.v3.limitSize
public import Spec.google_golang_org.protobuf.proto.SizePb
public import Proof.go_etcd_io.raft.v3.PbEntryType
public import Proof.go_etcd_io.raft.v3.MsgOut
public import Proof.go_etcd_io.raft.v3.LimitSizeLemmas

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

/-- Three exits, each giving a different `n`:
- `len(ents) == 0`: the input comes straight back, `n = 0`.
- the loop's early `return ents[:limit]`: a two-index sub-slice, `n = limit`, the right half
  captured in the wand's closure.
- falling out of the loop: `n = |es|`, the input again.

(out_size C3) Each entry is weighed by `proto.Size(ents[i])` (`util.go:290,292`), `proto.SizePb` at
`Entry`'s registered instance (`pbEntryC_reg`, stated at `HasLC.hasLC`, so this proof is too). The
loop invariant tracks, when the entries are sized and `maxSize ≤ entsCutMax`, that `size` is the sum
of the sizes of `ents[:limit]` and that it is within `maxSize` unless `limit = 1`: each size is below
`2^33` (`entrySize_lt_of_ok`), so the running sum never wraps. -/
theorem limitSize.wp_proof
    (wp_SizePb : proto.SizePb.spec (GF := GF) (hG := hG)) :
    limitSize.spec (GF := GF) (hG := hG) := by
  intro sz s cs dq maxSize
  wp_start as H
  iNamed H
  iunfold entsPtsC at Hs
  icases Hs with ⟨%ls, Hs, #Hb, %Hz⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  ihave %Hbl := entsBigC_length _ _ $$ Hb
  wp_if_destruct
  · have Hnil : cs = [] := List.eq_nil_of_length_eq_zero (by rw [← Hbl, Hlen.1]; word)
    subst Hnil
    iapply HΦ $$ %s %0
    simp only [List.take_zero]
    isplitr
    · ipureintro; exact ⟨by simp, fun h => absurd rfl h, fun _ _ => Or.inr (by simp)⟩
    isplitl
    · iunfold entsPtsC; iexists ls; iframe Hs Hb; ipureintro; exact Hz
    · iintro H; iexact H
  have Hne : 0 < cs.length := by rw [← Hbl, Hlen.1]; word
  obtain ⟨c0, Hc0⟩ : ∃ c0, cs[0]? = some c0 :=
    ⟨cs[0], List.getElem?_eq_getElem Hne⟩
  icases entsBigC_lookup ls cs 0 c0 Hc0 $$ Hb with ⟨%l0, %Hl0, #Hl0⟩
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) ls dq l0 (by word) $$ [Hs] as Hs
  · iframe; ipureintro; exact Hl0
  have wpS0 := wp_SizePb pbEntryC pbEntryC_reg l0 c0
  simp only [pbEntryC_ty, pbEntryC_roC, pbEntryC_size] at wpS0
  wp_apply wpS0 $$ [$Hl0] as %n0 %Hn0
  have Hsz0 : sz = true → uint.nat maxSize ≤ entsCutMax → uint.nat n0 = entrySize c0 := by
    intro h1 _
    have hok := Hz h1 c0 (List.mem_of_getElem? Hc0)
    have hlt := entrySize_lt_of_ok c0 hok
    have := Hn0 (by omega)
    word
  ihave IH : (∃ (lim acc : w64),
      "limit" ∷ limit_ptr ↦ lim ∗
      "size" ∷ size_ptr ↦ acc ∗
      "%Hlim" ∷ ⌜1 ≤ sint.Z lim ∧ sint.Z lim ≤ (cs.length : Int) ∧
        (sz = true → uint.nat maxSize ≤ entsCutMax →
          uint.nat acc = ((cs.take (sint.nat lim)).map entrySize).sum ∧
          (sint.nat lim = 1 ∨ uint.nat acc ≤ uint.nat maxSize))⌝) $$ [limit size]
  · iexists _, _
    iframe limit size
    ipureintro
    refine ⟨by word, by word, fun h1 h2 => ⟨?_, Or.inl (by word)⟩⟩
    rw [Hsz0 h1 h2, show sint.nat (W64 1) = 0 + 1 from rfl, entrySize_sum_take_succ cs 0 c0 Hc0]
    simp
  wp_for IH
  wp_if_destruct
  · obtain ⟨c, Hc⟩ : ∃ c, cs[(sint.Z lim).toNat]? = some c :=
      ⟨cs[(sint.Z lim).toNat]'(by word), List.getElem?_eq_getElem _⟩
    icases entsBigC_lookup ls cs _ c Hc $$ Hb with ⟨%l, %Hl, #Hl⟩
    rw [ite_eq_left ⟨by word, by word⟩]
    wp_apply wp_load_slice_index s (sint.Z lim) ls dq l (by word) $$ [Hs] as Hs
    · iframe; ipureintro; exact Hl
    have wpS := wp_SizePb pbEntryC pbEntryC_reg l c
    simp only [pbEntryC_ty, pbEntryC_roC, pbEntryC_size] at wpS
    wp_apply wpS $$ [$Hl] as %ni %Hni
    -- the new sum, exact when sized and `maxSize ≤ entsCutMax`
    have Hsum : sz = true → uint.nat maxSize ≤ entsCutMax →
        uint.nat (acc + ni) = ((cs.take (sint.nat (lim + W64 1))).map entrySize).sum := by
      intro h1 h2
      have hok := Hz h1 c (List.mem_of_getElem? Hc)
      have hlt := entrySize_lt_of_ok c hok
      have Hni' := Hni (by omega)
      obtain ⟨Ha, Hcut⟩ := Hlim.2.2 h1 h2
      have hc0 := Hz h1 c0 (List.mem_of_getElem? Hc0)
      have hlt0 := entrySize_lt_of_ok c0 hc0
      have Hacc : uint.nat acc < 2 ^ 33 := by
        rcases Hcut with h | h
        · rw [Ha, h, show (1 : Nat) = 0 + 1 from rfl, entrySize_sum_take_succ cs 0 c0 Hc0]
          simp; omega
        · unfold entsCutMax at h2; omega
      have hidx : sint.nat (lim + W64 1) = (sint.Z lim).toNat + 1 := by word
      rw [hidx, entrySize_sum_take_succ cs _ c Hc, ← show sint.nat lim = (sint.Z lim).toNat from rfl,
        ← Ha]
      word
    wp_if_destruct
    · rw [ite_eq_left ⟨by word, by word, by word⟩]
      wp_auto
      wp_for_post
      icases (ownSlice_split_all lim s dq ls ⟨by word, by word⟩).1 $$ Hs with ⟨Hs1, Hs2⟩
      iapply HΦ $$ %(slice.slice s Loc (W64 0) lim) %(sint.nat lim)
      isplitr
      · ipureintro
        refine ⟨by word, fun _ => by word, fun h1 h2 => ?_⟩
        obtain ⟨Ha, Hcut⟩ := Hlim.2.2 h1 h2
        unfold entsCut
        rcases Hcut with h | h
        · left; rw [List.length_take, h]; omega
        · right; rw [← Ha]; exact h
      isplitl [Hs1]
      · iunfold entsPtsC
        iexists ls.take (sint.nat lim)
        iframe Hs1
        isplitl
        · iapply entsBigC_take $$ Hb
        · ipureintro; intro h c' hc'; exact Hz h c' (List.mem_of_mem_take hc')
      iintro Hs1
      iunfold entsPtsC at Hs1
      icases Hs1 with ⟨%ls', Hs1, #Hb', -⟩
      ihave %Hbl' := entsBigC_length _ _ $$ Hb'
      ihave Hs := ownSlice_combine lim s dq ls' (ls.drop (sint.nat lim))
        (W64 0) s.len ⟨by rw [Hbl', List.length_take]; word, by word, by word, by word⟩ $$ Hs1 Hs2
      ihave Hs := ownSlice_trivial_slice_2 _ _ _ $$ Hs
      iunfold entsPtsC
      iexists ls' ++ ls.drop (sint.nat lim)
      iframe Hs
      ihave #Hd := entsBigC_drop (sint.nat lim) ls cs $$ Hb
      ihave Ha := entsBigC_app ls' (ls.drop (sint.nat lim)) (cs.take (sint.nat lim))
        (cs.drop (sint.nat lim)) $$ [Hb' Hd]
      · iframe Hb' Hd
      rw [List.take_append_drop]
      iframe Ha
      ipureintro; exact Hz
    · wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, fun h1 h2 => ⟨Hsum h1 h2, Or.inr ?_⟩⟩
      rename_i Hgt
      word
  · iapply HΦ $$ %s %cs.length
    have Hle : sint.nat lim = cs.length := by word
    rw [List.take_length]
    isplitr
    · ipureintro
      refine ⟨Nat.le_refl _, fun _ => Hne, fun h1 h2 => ?_⟩
      obtain ⟨Ha, Hcut⟩ := Hlim.2.2 h1 h2
      rw [Hle, List.take_length] at Ha
      unfold entsCut
      rcases Hcut with h | h
      · left; omega
      · right; rw [← Ha]; exact h
    isplitl
    · iunfold entsPtsC; iexists ls; iframe Hs Hb; ipureintro; exact Hz
    · iintro H; iexact H

end proof

end EtcdGrove
end Perennial

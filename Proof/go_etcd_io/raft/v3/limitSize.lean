/- Port of election_proof/proof_limitSize.v. -/
module

public import Spec.go_etcd_io.raft.v3.limitSize
public import Spec.google_golang_org.protobuf.proto.SizeEntry

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

/-- Three exits, each giving a different `n`:
- `len(ents) == 0`: the input comes straight back. `es = []`, so `take 0 es = es` and
  any `n` would do; `0` is chosen.
- the loop's early `return ents[:limit]`: a two-index sub-slice, so `n = limit` and the
  result is `ownSlice_split_all`'s left half (of the pointers; the entries' `entRO`s are
  persistent and taken along), with the right half captured in the wand's closure.
- falling out of the loop: `n = |es|`, the input again.

The loop invariant is just the two mutable locations plus `1 <= limit <= |es|`; nothing
about `size`, since the spec says nothing about where the cut falls. raft v3.7: each entry is
weighed by `proto.Size(ents[i])` (`util.go:290,292`), on the loaded pointer's `entRO`. -/
theorem limitSize.wp_proof
    (wp_proto_SizeEntry : proto.SizeEntry.spec (GF := GF) (hG := hG)) :
    limitSize.spec (GF := GF) (hG := hG) := by
  intro s es dq maxSize
  wp_start as H
  iNamed H
  iunfold entsPts at Hs
  icases Hs with ⟨%ls, Hs, #Hb⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  ihave %Hbl := entsBig_length $$ Hb
  wp_if_destruct
  · have Hnil : es = [] := List.eq_nil_of_length_eq_zero (by rw [← Hbl, Hlen.1]; word)
    subst Hnil
    iapply HΦ $$ %s %0
    simp only [List.take_zero]
    isplitr
    · ipureintro; exact ⟨by simp, fun h => absurd rfl h⟩
    isplitl
    · iunfold entsPts; iexists ls; iframe Hs Hb
    · iintro H; iexact H
  have Hne : 0 < es.length := by rw [← Hbl, Hlen.1]; word
  obtain ⟨e0, He0⟩ : ∃ e0, es[0]? = some e0 :=
    ⟨es[0], List.getElem?_eq_getElem Hne⟩
  icases entsBig_lookup ls es 0 e0 He0 $$ Hb with ⟨%l0, %Hl0, #Hl0⟩
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) ls dq l0 (by word) $$ [Hs] as Hs
  · iframe; ipureintro; exact Hl0
  wp_apply wp_proto_SizeEntry l0 DFrac.discard e0 $$ [$Hl0] as %sz0 ⟨-, -⟩
  ihave IH : (∃ (lim sz : w64),
      "limit" ∷ limit_ptr ↦ lim ∗
      "size" ∷ size_ptr ↦ sz ∗
      "%Hlim" ∷ ⌜1 ≤ sint.Z lim ∧ sint.Z lim ≤ (es.length : Int)⌝) $$ [limit size]
  · iexists _, _
    iframe limit size
    ipureintro; word
  wp_for IH
  wp_if_destruct
  · obtain ⟨e, He⟩ : ∃ e, es[(sint.Z lim).toNat]? = some e :=
      ⟨es[(sint.Z lim).toNat]'(by word), List.getElem?_eq_getElem _⟩
    icases entsBig_lookup ls es _ e He $$ Hb with ⟨%l, %Hl, #Hl⟩
    rw [ite_eq_left ⟨by word, by word⟩]
    wp_apply wp_load_slice_index s (sint.Z lim) ls dq l (by word) $$ [Hs] as Hs
    · iframe; ipureintro; exact Hl
    wp_apply wp_proto_SizeEntry l DFrac.discard e $$ [$Hl] as %szi ⟨-, -⟩
    wp_if_destruct
    · rw [ite_eq_left ⟨by word, by word, by word⟩]
      wp_auto
      wp_for_post
      icases (ownSlice_split_all lim s dq ls ⟨by word, by word⟩).1 $$ Hs with ⟨Hs1, Hs2⟩
      iapply HΦ $$ %(slice.slice s Loc (W64 0) lim) %(sint.nat lim)
      isplitr
      · ipureintro; exact ⟨by word, fun _ => by word⟩
      isplitl [Hs1]
      · iunfold entsPts
        iexists ls.take (sint.nat lim)
        iframe Hs1
        iapply entsBig_take $$ Hb
      iintro Hs1
      iunfold entsPts at Hs1
      icases Hs1 with ⟨%ls', Hs1, #Hb'⟩
      ihave %Hbl' := entsBig_length $$ Hb'
      ihave Hs := ownSlice_combine lim s dq ls' (ls.drop (sint.nat lim))
        (W64 0) s.len ⟨by rw [Hbl', List.length_take]; word, by word, by word, by word⟩ $$ Hs1 Hs2
      ihave Hs := ownSlice_trivial_slice_2 _ _ _ $$ Hs
      iunfold entsPts
      iexists ls' ++ ls.drop (sint.nat lim)
      iframe Hs
      ihave #Hd := entsBig_drop (sint.nat lim) ls es $$ Hb
      ihave Ha := entsBig_app ls' (ls.drop (sint.nat lim)) (es.take (sint.nat lim))
        (es.drop (sint.nat lim)) $$ [Hb' Hd]
      · iframe Hb' Hd
      rw [List.take_append_drop]
      iexact Ha
    · wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro; word
  · iapply HΦ $$ %s %es.length
    rw [List.take_length]
    isplitr
    · ipureintro; exact ⟨Nat.le_refl _, fun _ => Hne⟩
    isplitl
    · iunfold entsPts; iexists ls; iframe Hs Hb
    · iintro H; iexact H

end proof

end EtcdGrove
end Perennial

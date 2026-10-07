/- Port of election_proof/proof_limitSize.v. -/
import EtcdGrove.Raft.Spec.limitSize
import EtcdGrove.Raft.Spec.Entry__Size

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit [GoGlobalContext] in
/-- Rocq `list_insert_id`. -/
private theorem list_set_id {A : Type} (l : List A) (i : Nat) (x : A) (h : l[i]? = some x) :
    l.set i x = l := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 h
  exact List.set_getElem_self hlt

/-- Three exits, each giving a different `n`:
- `len(ents) == 0`: the input comes straight back. `es = []`, so `take 0 es = es` and
  any `n` would do; `0` is chosen.
- the loop's early `return ents[:limit]`: a two-index sub-slice, so `n = limit` and the
  result is `ownSlice_split_all`'s left half, with the right half captured in the
  wand's closure. This is the only `return` out of a `for:` body on the log path.
- falling out of the loop: `n = |es|`, the input again.

The loop invariant is just the two mutable locations plus `1 <= limit <= |es|`; nothing
about `size`, since the spec says nothing about where the cut falls. `Entry.Size` has a
pointer receiver applied to `&ents[i]`, not to a loaded value, so the element points-to
comes from `ownSlice_elem_acc` and goes back with `List.set_getElem_self`. -/
theorem limitSize.wp_proof
    (wp_Entry_Size : raftpb.Entry.Size.spec (GF := GF) (hG := hG)) :
    limitSize.spec (GF := GF) (hG := hG) := by
  intro s es dq maxSize
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hs
  wp_if_destruct
  · have Hnil : es = [] := List.eq_nil_of_length_eq_zero (by rw [Hlen.1]; word)
    subst Hnil
    iapply HΦ $$ %s %0
    simp only [List.take_zero]
    iframe Hs
    isplitr
    · ipureintro; exact ⟨by simp, fun h => absurd rfl h⟩
    · iintro H; iexact H
  have Hne : 0 < es.length := by rw [Hlen.1]; word
  obtain ⟨e0, He0⟩ : ∃ e0, es[0]? = some e0 :=
    ⟨es[0], List.getElem?_eq_getElem Hne⟩
  rw [ite_eq_left ⟨by word, by word⟩]
  icases ownSlice_elem_acc (sint.Z (W64 0)) e0 s dq es (by word) (by simpa using He0) $$ Hs
    with ⟨He, Hsback⟩
  wp_auto
  wp_apply wp_Entry_Size $$ [$He] as %sz0 He
  ihave Hs := Hsback $$ He
  rw [show (sint.Z (W64 0)).toNat = 0 from rfl, list_set_id es 0 e0 He0]
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
    rw [ite_eq_left ⟨by word, by word⟩]
    icases ownSlice_elem_acc (sint.Z lim) e s dq es (by word) He $$ Hs with ⟨He, Hsback⟩
    wp_auto
    wp_apply wp_Entry_Size $$ [$He] as %szi He
    ihave Hs := Hsback $$ He
    rw [list_set_id es _ e He]
    wp_if_destruct
    · rw [ite_eq_left ⟨by word, by word, by word⟩]
      wp_auto
      wp_for_post
      icases (ownSlice_split_all lim s dq es ⟨by word, by word⟩).1 $$ Hs with ⟨Hs1, Hs2⟩
      iapply HΦ $$ %(slice.slice s raftpb.Entry (W64 0) lim) %(sint.nat lim)
      iframe Hs1
      isplitr
      · ipureintro; exact ⟨by word, fun _ => by word⟩
      iintro Hs1
      ihave Hs := ownSlice_combine lim s dq (es.take (sint.nat lim)) (es.drop (sint.nat lim))
        (W64 0) s.len ⟨by rw [List.length_take]; word, by word, by word, by word⟩ $$ Hs1 Hs2
      rw [List.take_append_drop]
      iapply ownSlice_trivial_slice_2 $$ Hs
    · wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro; word
  · iapply HΦ $$ %s %es.length
    rw [List.take_length]
    iframe Hs
    isplitr
    · ipureintro; exact ⟨Nat.le_refl _, fun _ => Hne⟩
    · iintro H; iexact H

end proof

end EtcdGrove
end Perennial

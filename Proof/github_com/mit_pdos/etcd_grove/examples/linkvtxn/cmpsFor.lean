/-
Lean-first (no Rocq counterpart).

The proof of `cmpsFor`: `cmpsOf`, then the loop appends `cmpOf` of each comparison; its
invariant, the comparisons so far modelled by the decoded prefix.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.cmpsFor
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.cmpOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.cmpsOf

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem cmpsFor.wp_proof (wp_cmpsOf : cmpsOf.spec (GF := GF) (hG := hG))
    (wp_cmpOf : cmpOf.spec (GF := GF) (hG := hG)) :
    cmpsFor.spec (GF := GF) (hG := hG) := by
  intro x cs hcs hn
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply wp_slice_make3 (V := go_etcd_io.etcd.client.v3.Cmp) (W64 0) x.NCmps' ⟨by word, hn⟩
    as %o0 ⟨Ho, Hocap, -⟩
  rw [List.replicate_zero]
  (try wp_auto)
  wp_apply wp_cmpsOf x as %sl ⟨Hcs, -⟩
  ihave %Hl := ownSlice_len $$ Hcs
  have hml : cs.length = (cmpsOfL x).length := decAll_length _ _ _ hcs
  (try wp_auto)
  ihave HI : (∃ (j : w64) (c1 : Cmp) (os : GoSlice) (vs : List go_etcd_io.etcd.client.v3.Cmp),
      "i" ∷ i_ptr ↦ j ∗ "c" ∷ c_ptr ↦ c1 ∗ "cmps" ∷ cmps_ptr ↦ os ∗ "Hos" ∷ os ↦* vs ∗
      "Hoscap" ∷ ownSliceCap go_etcd_io.etcd.client.v3.Cmp os (DFrac.own 1) ∗
      "#Hel" ∷ □ (∀ (k : Nat) (v : go_etcd_io.etcd.client.v3.Cmp) (o : CmpModel), ⌜vs[k]? = some v⌝ -∗
        ⌜((cs.take (sint.nat j)).map linkv.cmpOf)[k]? = some o⌝ -∗ cmpAt v o) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧ vs.length = sint.nat j⌝ : IProp GF)
    $$ [i c cmps Ho Hocap]
  · iexists W64 0, _, o0, []
    iframe
    isplitl
    · imodintro
      iintro %k %v %o %Hv
      simp at Hv
    · ipureintro; exact ⟨by word, by word, rfl⟩
  wp_for HI
  by_cases Hif : sint.Z j < sint.Z sl.len
  · (try simp only [decide_eq_true Hif]); wp_pures; cleanup_bool_decide
    (try wp_auto); cleanup_bool_decide
    list_elem (cmpsOfL x) (sint.nat j) as c
    rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨Hj.1, Hif⟩)]
    wp_apply wp_load_slice_index sl (sint.Z j) (cmpsOfL x) (DFrac.own 1) c Hj.1 $$ [Hcs] as Hcs
    · iframe; ipureintro; exact Hc_lookup
    obtain ⟨m, hm, hmj⟩ := decAll_getElem decCmp (cmpsOfL x) cs hcs (sint.nat j) c Hc_lookup
    (try wp_auto)
    wp_apply wp_cmpOf c m hm $$ [] as %v #Hv
    · iframe #
    wp_apply wp_slice_literal (l := [v])
    isplitr
    · ipureintro; rfl
    iintro %lsl ⟨Hl1, _⟩
    wp_apply wp_slice_append $$ [$Hos $Hoscap $Hl1] as %os' ⟨Hos, Hoscap, -⟩
    wp_for_post
    iframe
    iexists j + W64 1, _, os', vs ++ [v]
    iframe
    isplitl
    · imodintro
      iintro %k %v' %o %Hv' %Ho
      have Htk : (cs.take (sint.nat (j + W64 1))).map linkv.cmpOf =
          (cs.take (sint.nat j)).map linkv.cmpOf ++ [linkv.cmpOf m] := by
        rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, hmj]
        simp
      rw [Htk] at Ho
      have hjm : sint.nat j < cs.length := by rw [hml, Hl.1]; word
      have hlt : ((cs.take (sint.nat j)).map linkv.cmpOf).length = vs.length := by
        rw [List.length_map, List.length_take, Nat.min_eq_left (Nat.le_of_lt hjm), Hj.2.2]
      by_cases hk : k < vs.length
      · rw [List.getElem?_append_left hk] at Hv'
        rw [List.getElem?_append_left (by rw [hlt]; exact hk)] at Ho
        iapply Hel $$ %k %v' %o %Hv' %Ho
      · have hk' : k = vs.length := by
          have := (List.getElem?_eq_some_iff.1 Hv').1
          simp only [List.length_append, List.length_singleton] at this
          omega
        subst hk'
        rw [List.getElem?_append_right (Nat.le_refl _)] at Hv'
        rw [List.getElem?_append_right (by rw [hlt]; exact Nat.le_refl _), hlt] at Ho
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at Hv' Ho
        subst Hv' Ho
        iexact Hv
    · ipureintro
      simp only [List.length_append, List.length_singleton]
      word
  · (try simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte]); wp_pures
    cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
    have hall : cs.take (sint.nat j) = cs := List.take_of_length_le (by rw [hml, Hl.1]; word)
    have hall' : cs.map linkv.cmpOf = (cs.take (sint.nat j)).map linkv.cmpOf := by rw [hall]
    rw [hall']
    ipersist Hos
    imodintro
    iapply HΦ
    unfold cmpsAt
    iexists vs
    iframe Hos
    isplitr
    · ipureintro; rw [List.length_map, hall, hml, Hl.1, Hj.2.2]; word
    iexact Hel

end proof

end linkvtxn
end EtcdGrove
end Perennial

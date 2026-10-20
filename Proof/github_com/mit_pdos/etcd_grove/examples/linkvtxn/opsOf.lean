/-
Lean-first (no Rocq counterpart).

The proof of `opsOf`: the loop appends `opOf` of each operation; its invariant, the operations
so far modelled by the decoded prefix.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.opsOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.opOf

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

/-- Decoding every element: the elements' decodings, index by index. -/
theorem decAll_getElem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (l' : List β), decAll f l = some l' →
      ∀ (k : Nat) (a : α), l[k]? = some a → ∃ b, f a = some b ∧ l'[k]? = some b
  | [], l', _, k, a, h => by simp at h
  | x :: l, l', h, k, a, hk => by
    simp only [decAll] at h
    cases hf : f x with
    | none => rw [hf] at h; cases h
    | some b =>
      rw [hf] at h
      cases hr : decAll f l with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          exact ⟨b, hf, rfl⟩
        | succ k =>
          simp only [List.getElem?_cons_succ] at hk ⊢
          exact decAll_getElem f l r hr k a hk

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem opsOf.wp_proof (wp_opOf : opOf.spec (GF := GF) (hG := hG)) :
    opsOf.spec (GF := GF) (hG := hG) := by
  intro sl ops dq ms hms
  wp_start as Hops
  iapply wp_fupd
  ihave %Hl := ownSlice_len $$ Hops
  have hml : ms.length = ops.length := decAll_length _ _ _ hms
  wp_auto
  wp_apply wp_slice_make3 (V := go_etcd_io.etcd.client.v3.Op) (W64 0) sl.len ⟨by word, by word⟩
    as %o0 ⟨Ho, Hocap, -⟩
  rw [List.replicate_zero]
  ihave HI : (∃ (j : w64) (o1 : TOp) (os : GoSlice) (vs : List go_etcd_io.etcd.client.v3.Op),
      "i" ∷ i_ptr ↦ j ∗ "op" ∷ op_ptr ↦ o1 ∗ "out" ∷ out_ptr ↦ os ∗ "Hos" ∷ os ↦* vs ∗
      "Hoscap" ∷ ownSliceCap go_etcd_io.etcd.client.v3.Op os (DFrac.own 1) ∗
      "#Hel" ∷ □ (∀ (k : Nat) (v : go_etcd_io.etcd.client.v3.Op) (o : OpFull), ⌜vs[k]? = some v⌝ -∗
        ⌜((ms.take (sint.nat j)).map clientOp)[k]? = some o⌝ -∗ opFullAt v o) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧ vs.length = sint.nat j⌝ : IProp GF)
    $$ [i op out Ho Hocap]
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
    list_elem ops (sint.nat j) as x
    rw [if_pos (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len from ⟨Hj.1, Hif⟩)]
    wp_apply wp_load_slice_index sl (sint.Z j) ops dq x Hj.1 $$ [Hops] as Hops
    · iframe; ipureintro; exact Hx_lookup
    obtain ⟨m, hm, hmj⟩ := decAll_getElem decTOp ops ms hms (sint.nat j) x Hx_lookup
    (try wp_auto)
    wp_apply wp_opOf x m hm $$ [] as %v #Hv
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
      have Htk : (ms.take (sint.nat (j + W64 1))).map clientOp =
          (ms.take (sint.nat j)).map clientOp ++ [clientOp m] := by
        rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, hmj]
        simp
      rw [Htk] at Ho
      have hjm : sint.nat j < ms.length := by rw [hml, Hl.1]; word
      have hlt : ((ms.take (sint.nat j)).map clientOp).length = vs.length := by
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
    have hall : ms.take (sint.nat j) = ms := List.take_of_length_le (by word)
    have hall' : ms.map clientOp = (ms.take (sint.nat j)).map clientOp := by rw [hall]
    rw [hall']
    ipersist Hos
    imodintro
    iapply HΦ
    iframe
    unfold opsAt
    iexists vs
    iframe Hos
    isplitr
    · ipureintro; rw [List.length_map, hall, hml, Hl.1, Hj.2.2]; word
    iexact Hel

end proof

end linkvtxn
end EtcdGrove
end Perennial

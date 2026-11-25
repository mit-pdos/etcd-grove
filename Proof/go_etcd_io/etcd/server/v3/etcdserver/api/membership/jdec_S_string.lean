/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/jdec_S_string.lean` (jsongen's
generated code, membership's `json_model_gen.go`), over `models.lab/jsoncodec`'s decoding helpers.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.jdec_S_string
public import Net.Spec.models_lab.jsoncodec.At
public import Net.Spec.models_lab.jsoncodec.Empty
public import Net.Spec.models_lab.jsoncodec.Next
public import Net.Spec.models_lab.jsoncodec.String
public import Net.Proof.models_lab.jsoncodec.DecBase

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode models_lab.jsoncodec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.membership.Assumptions]

set_option goose.wp.extras true

open go_etcd_io.etcd.server.v3.etcdserver.api in
theorem membership.jdec_S_string.wp_proof
    (wp_At : models_lab.jsoncodec.At.spec (GF := GF) (hG := hG))
    (wp_Empty : models_lab.jsoncodec.Empty.spec (GF := GF) (hG := hG))
    (wp_Next : models_lab.jsoncodec.Next.spec (GF := GF) (hG := hG))
    (wp_String : models_lab.jsoncodec.String.spec (GF := GF) (hG := hG)) :
    membership.jdec_S_string.spec (GF := GF) (hG := hG) := by
  intro b dq bs i p e v xs rest hv hb
  wp_start as ⟨Hb, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hb
  have hl63 := len_lt b bs Hlen
  have hlen1 : ∀ (c : w8) (cs : List w8), v.json = c :: cs →
      bs[uint.nat i]? = some c ∧ uint.nat i + v.json.length ≤ bs.length := by
    intro c cs hc
    have h1 := congrArg List.length hb
    rw [List.length_drop, List.length_append, hc] at h1
    have h2 := congrArg (fun l => l[0]?) hb
    simp only [List.getElem?_drop, hc] at h2
    refine ⟨by simpa using h2, ?_⟩
    rw [hc]; simp at h1 ⊢; omega
  cases v with
  | null =>
    simp only [membership.strsOf, Option.some.injEq] at hv
    subst hv
    obtain ⟨h0, hle⟩ := hlen1 (W8 110) _ rfl
    have hsk : JsonScan.skipEnd bs (uint.nat i) = uint.nat i := skipEnd_ns' bs _ _ h0 (by decide)
    wp_auto
    wp_apply (wp_At b dq bs i (W8 110) (by omega) (by rw [hsk]; exact h0)) $$ Hb as Hb
    rw [hsk, show W64 ((uint.nat i : Nat) : Int) = i by word]
    try wp_auto
    rw [show i + W64 4 = W64 ((uint.nat i + (membership.JVal.null).json.length : Nat) : Int) by
      simp [membership.JVal.json]; word]
    iapply HΦ
    iframe
    iapply ownSlice_nil
  | arr ys =>
    by_cases hpl : ∀ x ∈ ys, membership.plainStr x
    case neg => simp only [membership.strsOf] at hv; rw [if_neg hpl] at hv; cases hv
    simp only [membership.strsOf] at hv; rw [if_pos hpl] at hv
    cases hv
    obtain ⟨h0, hle⟩ := hlen1 (W8 91) _ rfl
    have hsk : JsonScan.skipEnd bs (uint.nat i) = uint.nat i := skipEnd_ns' bs _ _ h0 (by decide)
    wp_auto
    wp_apply (wp_At b dq bs i (W8 91) (by omega) (by rw [hsk]; exact h0)) $$ Hb as Hb
    rw [hsk, show W64 ((uint.nat i : Nat) : Int) = i by word]
    try wp_auto
    have hb1 : bs.drop (uint.nat i + 1) = membership.jstrs xs ++ 93#8 :: rest := by
      have := congrArg (List.drop 1) hb
      simpa [List.drop_drop, Nat.add_comm, membership.JVal.json] using this
    cases xs with
    | nil =>
      have h1 : bs[uint.nat i + 1]? = some (W8 93) := by
        have := congrArg (fun l => l[0]?) hb1
        simp only [List.getElem?_drop] at this; simpa [membership.jstrs] using this
      have hsk1 : JsonScan.skipEnd bs (uint.nat i + 1) = uint.nat i + 1 :=
        skipEnd_ns' bs _ _ h1 (by decide)
      have hle' : uint.nat i + 2 ≤ bs.length := by
        simpa [membership.JVal.json, membership.jstrs] using hle
      wp_apply (wp_Empty b dq bs i (W8 93) (by omega) (by rw [hsk1]; exact h1)) $$ Hb as Hb
      rw [hsk1]
      try wp_auto
      wp_apply wp_slice_make2 (V := GoString) (W64 0) as %sl ⟨Hsl, -⟩
      · ipureintro; word
      try wp_auto
      rw [show W64 ((uint.nat i + 1 + 1 : Nat) : Int) =
          W64 ((uint.nat i + (membership.JVal.arr []).json.length : Nat) : Int) by
        simp [membership.JVal.json, membership.jstrs]; congr 1]
      iapply HΦ
      simp only [List.replicate_zero]
      iframe
    | cons y ys' =>
      have h1 : bs[uint.nat i + 1]? = some (W8 34) := by
        have := congrArg (fun l => l[0]?) hb1
        simp only [List.getElem?_drop] at this
        simpa [membership.jstrs_cons, membership.jquoted] using this
      have hsk1 : JsonScan.skipEnd bs (uint.nat i + 1) = uint.nat i + 1 :=
        skipEnd_ns' bs _ _ h1 (by decide)
      have hle' : uint.nat i + 2 ≤ bs.length := by
        have := congrArg List.length hb1
        rw [List.length_drop] at this; simp [membership.jstrs_cons, membership.jquoted] at this; omega
      wp_apply (wp_Empty b dq bs i (W8 34) (by omega) (by rw [hsk1]; exact h1)) $$ Hb as Hb
      try wp_auto
      wp_apply wp_slice_make2 (V := GoString) (W64 0) as %sl ⟨Hsl, Hcap⟩
      · ipureintro; word
      try wp_auto
      ihave HI : (∃ (done rem : List GoString) (sv : GoSlice) (kw : w64),
          "s" ∷ s_ptr ↦ sv ∗ "Hs" ∷ sv ↦* done ∗ "Hcap" ∷ ownSliceCap GoString sv (DFrac.own 1) ∗
          "k" ∷ k_ptr ↦ kw ∗
          "%Hinv" ∷ ⌜y :: ys' = done ++ rem ∧ rem ≠ [] ∧
            bs.drop (uint.nat kw) = membership.jstrs rem ++ 93#8 :: rest ∧
            uint.nat kw + (membership.jstrs rem).length + 1 =
              uint.nat i + (membership.JVal.arr (y :: ys')).json.length⌝ : IProp GF) $$ [s Hsl Hcap k]
      · iexists [], y :: ys', sl, i + W64 1
        simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
        iframe
        ipureintro
        have hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
        refine ⟨rfl, by simp, ?_, ?_⟩
        · rw [hi1]; exact hb1
        · rw [hi1]; simp [membership.JVal.json]; omega
      wp_for HI
      obtain ⟨Hxs, Hrem, Hdrop, Hk⟩ := Hinv
      obtain ⟨r0, rem', rfl⟩ : ∃ r0 rem', rem = r0 :: rem' := by
        cases rem with
        | nil => exact absurd rfl Hrem
        | cons a l => exact ⟨a, l, rfl⟩
      have hr0 : membership.plainStr r0 := hpl r0 (by rw [Hxs]; simp)
      wp_apply wp_slice_literal (V := GoString)
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hlsl, -⟩
      wp_apply wp_slice_append (V := GoString) _ _ _ _ _ $$ [$Hs $Hcap $Hlsl] as %s1 ⟨Hs, Hcap, -⟩
      ihave %Hs1len := ownSlice_len $$ Hs
      try wp_auto
      have hsep : bs.drop (uint.nat kw) = 34#8 :: (r0 ++ 34#8 ::
          ((if rem' = [] then [] else 44#8 :: membership.jstrs rem') ++ 93#8 :: rest)) := by
        rw [Hdrop, membership.jstrs_cons]; simp [membership.jquoted]
      have hklen : uint.nat kw + r0.length + 2 + (if rem' = [] then 0 else 1 + (membership.jstrs rem').length)
          + 1 ≤ bs.length := by
        have := congrArg List.length hsep
        rw [List.length_drop] at this
        simp only [List.length_cons, List.length_append] at this
        by_cases hr : rem' = [] <;>
          simp only [hr, ↓reduceIte, List.length_nil, List.length_cons] at this ⊢ <;> omega
      wp_apply (wp_String b dq bs kw r0 _ hr0 hsep) $$ Hb as Hb
      try wp_auto
      have hn : sint.Z (s1.len - W64 1) = (done.length : Int) := by
        simp only [List.length_append, List.length_singleton] at Hs1len; word
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by word⟩)]
      wp_apply wp_store_slice_index s1 _ _ r0 $$ [Hs] as Hs
      · iframe; ipureintro; simp only [List.length_append, List.length_singleton]; omega
      rw [hn, show ((done.length : Int)).toNat = done.length by omega,
        List.set_append_right _ _ (by omega)] at *
      simp only [Nat.sub_self, List.set_cons_zero]
      try wp_auto
      have hk1 : uint.nat (W64 ((uint.nat kw + 1 + r0.length + 1 : Nat) : Int)) =
          uint.nat kw + r0.length + 2 := by
        have : uint.nat kw + r0.length + 2 < 2 ^ 63 := by omega
        word
      have hsep2 : bs.drop (uint.nat kw + r0.length + 2) =
          (if rem' = [] then [] else 44#8 :: membership.jstrs rem') ++ 93#8 :: rest := by
        have := congrArg (List.drop (r0.length + 2)) hsep
        rw [List.drop_drop] at this
        rw [show uint.nat kw + r0.length + 2 = uint.nat kw + (r0.length + 2) by omega, this]
        simp
      by_cases hr : rem' = []
      · subst hr
        have hc : bs[uint.nat kw + r0.length + 2]? = some (W8 93) := by
          have := congrArg (fun l => l[0]?) hsep2
          simp only [List.getElem?_drop] at this; simpa using this
        have hskc := skipEnd_ns' bs _ _ hc (by decide)
        wp_apply (wp_Next b dq bs _ (W8 93) (by rw [hk1]; omega) (by rw [hk1, hskc]; exact hc))
          $$ Hb as Hb
        rw [hk1, hskc]
        try simp only [show decide (W8 93 = W8 44) = false by decide]
        try wp_auto
        wp_for_post
        rw [show W64 ((uint.nat kw + r0.length + 2 + 1 : Nat) : Int) =
            W64 ((uint.nat i + (membership.JVal.arr (y :: ys')).json.length : Nat) : Int) by
          congr 2; simp [membership.jstrs, membership.jquoted] at Hk; omega]
        iapply HΦ
        rw [Hxs]
        iframe
      · have hc : bs[uint.nat kw + r0.length + 2]? = some (W8 44) := by
          have := congrArg (fun l => l[0]?) hsep2
          simp only [List.getElem?_drop, hr, ↓reduceIte] at this; simpa using this
        have hskc := skipEnd_ns' bs _ _ hc (by decide)
        wp_apply (wp_Next b dq bs _ (W8 44) (by rw [hk1]; omega) (by rw [hk1, hskc]; exact hc))
          $$ Hb as Hb
        rw [hk1, hskc]
        try simp only [show decide (W8 44 = W8 44) = true by decide]
        try wp_auto
        wp_for_post
        iframe
        iexists done ++ [r0], rem', s1, W64 ((uint.nat kw + r0.length + 2 + 1 : Nat) : Int)
        iframe
        ipureintro
        have hk2 : uint.nat (W64 ((uint.nat kw + r0.length + 2 + 1 : Nat) : Int)) =
            uint.nat kw + r0.length + 3 := by
          have : uint.nat kw + r0.length + 3 < 2 ^ 63 := by omega
          word
        refine ⟨by rw [Hxs]; simp, hr, ?_, ?_⟩
        · rw [hk2]
          have := congrArg (List.drop 1) hsep2
          rw [List.drop_drop] at this
          rw [show uint.nat kw + r0.length + 3 = uint.nat kw + r0.length + 2 + 1 by omega, this]
          simp [hr]
        · rw [hk2, ← Hk, membership.jstrs_cons]
          simp [hr, membership.jquoted]; omega
  | num n => simp [membership.strsOf] at hv
  | str s => simp [membership.strsOf] at hv
  | bool x => simp [membership.strsOf] at hv

end proof

end EtcdGrove
end Perennial

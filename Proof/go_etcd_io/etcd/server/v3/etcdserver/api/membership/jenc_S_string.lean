/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/jenc_S_string.lean` (jsongen's generated
code, membership's `json_model_gen.go`), over `models.lab/jsoncodec`'s proved helpers.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.jenc_S_string
public import Net.Spec.models_lab.jsoncodec.AppendString
public import Net.Spec.models_lab.jsoncodec.AppendRaw

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
theorem membership.jenc_S_string.wp_proof
    (wp_AppendString : models_lab.jsoncodec.AppendString.spec (GF := GF) (hG := hG))
    (wp_AppendRaw : models_lab.jsoncodec.AppendRaw.spec (GF := GF) (hG := hG)) :
    membership.jenc_S_string.spec (GF := GF) (hG := hG) := by
  intro b bs v dq xs d hd
  wp_start as ⟨Hb, Hcap, Hv⟩
  wp_auto
  wp_if_destruct
  · wp_apply wp_AppendRaw $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    try wp_auto
    iapply HΦ
    iframe
  · wp_if_destruct
    · exfalso
      have : uint.Z (W64 1000) = 1000 := rfl
      omega
    · wp_apply wp_slice_literal (V := w8)
      isplitr
      · ipureintro; rfl
      iintro %lsl ⟨Hlsl, -⟩
      wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlsl] as %b1 ⟨Hb, Hcap, -⟩
      try wp_auto
      wp_pures
      rename_i gip
      irename : (gip ↦ (zero_val w64 : w64)) => gi
      ihave %Hvlen := ownSlice_len _ _ _ $$ Hv
      ihave HI : (∃ (k : w64) (o : GoSlice) (g : w64) (xv : GoString),
          "i" ∷ i_ptr ↦ k ∗ "gi" ∷ gip ↦ g ∗ "x" ∷ x_ptr ↦ xv ∗ "b" ∷ b_ptr ↦ o ∗
          "Hb" ∷ o ↦* (bs ++ [W8 91] ++ membership.jsonStrs (xs.take (sint.nat k))) ∗
          "Hcap" ∷ ownSliceCap w8 o (DFrac.own 1) ∗ "Hv" ∷ v ↦*{dq} xs ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ xs.length⌝ : IProp GF) $$ [i gi x b Hb Hcap Hv]
      · iexists (W64 0), b1, (zero_val w64 : w64), (zero_val GoString : GoString)
        simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, membership.jsonStrs,
          List.append_nil]
        iframe
        ipureintro
        exact ⟨by decide, by omega⟩
      wp_for HI
      by_cases hlt : sint.Z k < sint.Z v.len
      · simp only [hlt, decide_true, ↓reduceIte]
        have hkl : sint.nat k < xs.length := by rw [Hvlen.1]; word
        obtain ⟨xk, Hxk⟩ : ∃ xk, xs[sint.nat k]? = some xk := ⟨_, List.getElem?_eq_getElem hkl⟩
        wp_auto
        simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z v.len from ⟨Hk.1, hlt⟩]
        wp_apply wp_load_slice_index _ _ _ _ xk Hk.1 $$ [Hv] with Hv
        · iframe; ipureintro; exact Hxk
        try wp_auto
        have hstep := membership.jsonStrs_take_succ xs (sint.nat k) hkl
        have hxk : xs[sint.nat k] = xk := by
          rw [List.getElem?_eq_getElem hkl] at Hxk; exact Option.some.inj Hxk
        rw [hxk] at hstep
        have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
        wp_if_destruct
        · wp_apply wp_slice_literal (V := w8)
          isplitr
          · ipureintro; rfl
          iintro %lsl2 ⟨Hlsl, -⟩
          wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlsl] as %o1 ⟨Hb, Hcap, -⟩
          try wp_auto
          wp_apply wp_AppendString $$ [$Hb $Hcap] as %o2 ⟨Hb, Hcap⟩
          wp_for_post
          iframe
          iexists (k + W64 1), o2, k, xk
          iframe
          isplitl [Hb]
          · iapply (slice_pts_eq _ _ _ ?_) $$ Hb
            have hk0 : sint.nat k ≠ 0 := by word
            rw [hk1, hstep]
            simp only [hk0, ↓reduceIte, List.append_assoc]
          · ipureintro; exact ⟨by word, by word⟩
        · wp_apply wp_AppendString $$ [$Hb $Hcap] as %o2 ⟨Hb, Hcap⟩
          wp_for_post
          iframe
          iexists (k + W64 1), o2, k, xk
          iframe
          isplitl [Hb]
          · iapply (slice_pts_eq _ _ _ ?_) $$ Hb
            have hk0 : sint.nat k = 0 := by word
            rw [hk1, hstep]
            simp only [hk0, ↓reduceIte, List.append_assoc, List.append_nil]
          · ipureintro; exact ⟨by word, by word⟩
      · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
        try wp_auto
        wp_apply wp_slice_literal (V := w8)
        isplitr
        · ipureintro; rfl
        iintro %lsl2 ⟨Hlsl, -⟩
        wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlsl] as %o1 ⟨Hb, Hcap, -⟩
        try wp_auto
        iapply HΦ
        iframe
        iapply (slice_pts_eq _ _ _ ?_) $$ Hb
        have hke : sint.nat k = xs.length := by rw [Hvlen.1] at Hk ⊢; word
        rw [hke, List.take_length]
        simp only [membership.jsonStrSlice, Bool.false_eq_true, ↓reduceIte, List.append_assoc]

end proof

end EtcdGrove
end Perennial

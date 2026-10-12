/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.mkGteRange

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

set_option goose.wp.unfoldSliceLiterals true in
/-- Perennial's `wp_slice_literal`, also giving that the literal's array is not `null` (its
allocation's points-to): a slice literal, even `[]T{}`, is never `nil`. -/
theorem txn.wp_slice_literal_nn {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    {st t : go.GoType} [IntoValTyped (GF := GF) V t] [st ↓u go.SliceType t]
    (l : List V) (kvs : List keyed_element) (Φ : val → IProp GF) :
    WP (App (Val (GoInstruction (CompositeLiteral (go.ArrayType (go.arrayLiteralSize kvs) t))))
          (Val (LiteralValueV kvs)))
      {{ v, ⌜v = #(array.mk (go.arrayLiteralSize kvs) l)⌝ ∗
        (∀ sl_ptr : Loc, ⌜sl_ptr ≠ null⌝ -∗
          (slice.mk sl_ptr (W64 (go.arrayLiteralSize kvs)) (W64 (go.arrayLiteralSize kvs)) ↦* l ∗
            ownSliceCap V (slice.mk sl_ptr (W64 (go.arrayLiteralSize kvs))
              (W64 (go.arrayLiteralSize kvs))) (DFrac.own 1)) -∗
          Φ #(slice.mk sl_ptr (W64 (go.arrayLiteralSize kvs)) (W64 (go.arrayLiteralSize kvs)))) }} ⊢
    WP (App (Val (GoInstruction (CompositeLiteral st))) (Val (LiteralValueV kvs))) {{ Φ }} := by
  iintro HΦ
  wp_pures
  by_cases hlen : go.arrayLiteralSize kvs < 2 ^ 63
  · rw [ite_eq_left hlen]
    wp_pures
    wp_alloc_auto
    wp_pure
    wp_pure
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.ArrayType _ t)))) (Val (LiteralValueV kvs)))
    wp_apply_core wp_wand $$ HΦ
    iintro %v ⟨%Hv, HΦ⟩
    subst Hv
    wp_auto
    have h0 : 0 ≤ go.arrayLiteralSize kvs := by
      unfold go.arrayLiteralSize; split; omega
    rw [ite_eq_left ⟨by decide, by word, by word⟩]
    have hz : W64 (go.arrayLiteralSize kvs) - W64 0 = W64 (go.arrayLiteralSize kvs) := by word
    simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, hz]
    wp_pures
    ihave %Hlen := array_len _ _ _ _ $$ tmp
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ tmp
    iapply HΦ $$ %tmp_ptr %Hnn
    isplitl [tmp]
    · iapply slice_array tmp_ptr _ (array.mk (go.arrayLiteralSize kvs) l) (by simp only; omega)
      iexact tmp
    · iapply ownSliceCap_empty _ rfl (by simp only; word)
  · rw [ite_eq_right hlen]; iapply wp_AngelicExit

theorem txn.mkGteRange.wp_proof : txn.mkGteRange.spec (GF := GF) (hG := hG) := by
  intro sl e
  wp_start as #Hs
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  wp_auto
  have hnil : sl = slice.nil → e = [] := by
    intro h; subst h
    have := Hl.1; simp [slice.nil] at this; exact List.length_eq_zero_iff.1 this
  wp_if_destruct
  · have hlen : e.length = 1 := by rw [Hl.1, Hif]; rfl
    have hsl : sl ≠ slice.nil := by
      intro h; have := hnil h; subst this; simp at hlen
    obtain ⟨b, hb⟩ : ∃ b, e = [b] := by
      match e, hlen with
      | [b], _ => exact ⟨b, rfl⟩
    subst hb
    have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len := by rw [Hif]; decide
    simp only [Hb0, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index sl (sint.Z (W64 0)) [b] DFrac.discard b (by decide) $$ [$Hs] as -
    · ipureintro; rfl
    wp_if_destruct
    · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte)))) (Val (LiteralValueV _)))
      iapply txn.wp_slice_literal_nn (V := w8) (t := go.byte) []
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %sl_ptr %Hnn ⟨Hsl, -⟩
      ipersist Hsl
      wp_auto
      iapply HΦ
      iframe Hsl
      ipureintro
      simp [txn.rangeEndOf, txn.srvEnd, hsl, slice_mk_eq_nil, Hnn]
    · iapply HΦ
      iframe Hs
      ipureintro
      simp [txn.rangeEndOf, txn.srvEnd, hsl]
      exact Hif
  · iapply HΦ
    iframe Hs
    ipureintro
    by_cases h : sl = slice.nil
    · simp [txn.rangeEndOf, txn.srvEnd, h, hnil h]
    · have hne1 : e ≠ [W8 0] := by
        intro he; subst he; have := Hl.1; apply Hif; simp at this; word
      by_cases he : e = []
      · simp [txn.rangeEndOf, txn.srvEnd, h, he]
      · simp [txn.rangeEndOf, txn.srvEnd, h, he]
        exact hne1

end proof

end EtcdGrove
end Perennial

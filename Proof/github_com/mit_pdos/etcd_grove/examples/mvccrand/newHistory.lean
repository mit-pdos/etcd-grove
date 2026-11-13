/- Lean-first (no Rocq counterpart). The proof of `newHistory`: the slice literal of two empty
map literals (`wp_slice_literal`, each map literal `make1`), the slice of two `nil` change slices,
the struct allocated and split, `published` stored, and the ghost state of the revisions `hist0`
allocated (the slices' contents and the monotone list, each split between the lock's part and the
writer's). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.newHistory

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand

section slice_ex
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

set_option goose.wp.unfoldSliceLiterals true in
/-- `wp_slice_literal` with the elements chosen in the array literal's post (`∃ l`), so that they may
be values the elements' own WPs return (here the two maps `make1` allocates); a local copy of
Perennial's `wp_slice_literal_nonnull` proof (`notes/perennial-changes.md`, "A slice literal of map
literals"). -/
theorem wp_slice_literal_ex {st t : go.GoType} [IntoValTyped (GF := GF) V t]
    [st ↓u go.SliceType t] (kvs : List keyed_element) (Φ : val → IProp GF) :
    WP (App (Val (GoInstruction (CompositeLiteral (go.ArrayType (go.arrayLiteralSize kvs) t))))
          (Val (LiteralValueV kvs)))
      {{ v, ∃ l : List V, ⌜v = #(array.mk (go.arrayLiteralSize kvs) l)⌝ ∗
        (∀ sl_ptr : Loc,
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
    iintro %v ⟨%l, %Hv, HΦ⟩
    subst Hv
    wp_auto
    have h0 : 0 ≤ go.arrayLiteralSize kvs := by
      unfold go.arrayLiteralSize; split; omega
    rw [ite_eq_left ⟨by decide, by word, by word⟩]
    have hz : W64 (go.arrayLiteralSize kvs) - W64 0 = W64 (go.arrayLiteralSize kvs) := by word
    simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0, hz]
    wp_pures
    ihave %Hlen := array_len _ _ _ _ $$ tmp
    iapply HΦ $$ %tmp_ptr
    isplitl [tmp]
    · iapply slice_array tmp_ptr _ (array.mk (go.arrayLiteralSize kvs) l) (by simp only; omega)
      iexact tmp
    · iapply ownSliceCap_empty _ rfl (by simp only; word)
  · rw [ite_eq_right hlen]; iapply wp_AngelicExit

end slice_ex

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

theorem newHistory.wp_proof : newHistory.spec (GF := GF) (hG := hG) := by
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply (wp_slice_literal_ex (V := GoMap))
  wp_apply (wp_map_make1 (K := GoString) (V := kvRec)) as %m1 Hm1
  wp_apply (wp_map_make1 (K := GoString) (V := kvRec)) as %m2 Hm2
  iexists [m1, m2]
  isplitr
  · ipureintro; rfl
  iintro %ssl ⟨Hss, Hssc⟩
  wp_auto
  wp_apply (wp_slice_literal (V := GoSlice) [slice.nil, slice.nil])
  isplitr
  · ipureintro; rfl
  iintro %csl ⟨Hcs, Hcsc⟩
  wp_auto
  irename «$r0» => Hh
  generalize «$r0_ptr» = h at *
  iStructNamed Hh
  ihave Hpub : sync.atomic.ownInt64 (GF := GF) (hPub h) (DFrac.own 1) (W64 0) $$ [published]
  · rw [sync.atomic.ownInt64_unseal]
    unfold sync.atomic.ownInt64Def
    rw [show ({ «_#0'» := zero_val _, «_#1'» := zero_val _, v' := W64 0 } : sync.atomic.Int64) =
      zero_val _ from rfl]
    iexact published
  ihave Habove : sync.atomic.ownInt64 (GF := GF) (hAbove h) (DFrac.own 1) (W64 0) $$ [aboveFloor]
  · rw [sync.atomic.ownInt64_unseal]
    unfold sync.atomic.ownInt64Def
    rw [show ({ «_#0'» := zero_val _, «_#1'» := zero_val _, v' := W64 0 } : sync.atomic.Int64) =
      zero_val _ from rfl]
    iexact aboveFloor
  wp_apply_core sync.atomic.Int64.wp_Store (hPub h) (W64 1) $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iexists _
  iframe Hpub
  iintro Hpub
  imod Hcl
  imodintro
  wp_auto
  -- the cells' contents, persistently
  imod ownMap_persist $$ Hm1 with #Hm1
  imod ownMap_persist $$ Hm2 with #Hm2
  imod ownSlice_persist $$ Hss with #Hss
  imod ownSlice_persist $$ Hcs with #Hcs
  ihave #Hnil : (slice.nil ↦*□ ([] : List change) : IProp GF) $$ []
  · iapply ownSlice_nil
  let x : HistCells := (slice.mk ssl (W64 (go.arrayLiteralSize
      [KeyedElement none (ElementLiteralValue []), KeyedElement none (ElementLiteralValue [])]))
      (W64 (go.arrayLiteralSize
        [KeyedElement none (ElementLiteralValue []), KeyedElement none (ElementLiteralValue [])])),
    slice.mk csl (W64 (go.arrayLiteralSize
      [KeyedElement none (ElementExpression go.untypedNil UntypedNil),
        KeyedElement none (ElementExpression go.untypedNil UntypedNil)]))
      (W64 (go.arrayLiteralSize
        [KeyedElement none (ElementExpression go.untypedNil UntypedNil),
          KeyedElement none (ElementExpression go.untypedNil UntypedNil)])),
    [m1, m2], [slice.nil, slice.nil], hist0)
  imod ghostVar_alloc (GF := GF) x with ⟨%γg, Hg⟩
  icases ghostVar_split γg x (1 : Qp).half (1 : Qp).half $$ [Hg] with ⟨Hg1, Hg2⟩
  · rw [Qp.half_add_half]; iexact Hg
  imod mono_list_own_alloc (GF := GF) hist0 with ⟨%γl, Hl, -⟩
  ihave ⟨Hl1, Hl2⟩ : monoListAuthOwn (GF := GF) γl (1 : Qp).half hist0 ∗
      monoListAuthOwn (GF := GF) γl (1 : Qp).half hist0 $$ [Hl]
  · iapply ((monoListAuthOwn_fractional (GF := GF) γl hist0).fractional (1 : Qp).half (1 : Qp).half).1
    rw [Qp.half_add_half]; iexact Hl
  imodintro
  iapply HΦ
  iexists ⟨γg, γl⟩
  iframe mu Habove Hpub
  isplitl [states changes Hg1 Hl1]
  · iunfold histR
    iexists x
    iframe
    iunfold histElems
    iunfold statesP
    iunfold changesP
    simp only [hist0, x, List.zip_cons_cons, List.zip_nil_right, List.length_cons, List.length_nil]
    simp
    iframe #
  · iunfold histW
    iexists x
    iframe
    ipureintro; rfl

end proof

end mvccrand
end EtcdGrove
end Perennial

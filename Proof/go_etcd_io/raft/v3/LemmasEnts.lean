/-
Lemmas on read-only entry slices, conf-state and snapshot pointers, and slice literals (U8 v2,
2026-10-29: moved out of `LemmasMemstorage.lean`, which imports the `MemoryStorage` model, so that
raft's proofs use them without it).
-/
module

public import Proof.go_etcd_io.raft.v3.InvStorage

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The pointer at position `i` of a read-only entry slice, and the log entry behind it: what
`wp_load_slice_index` and an `Entry` getter need. Persistent, so the slice fact is kept. -/
theorem entsRO_lookup (s : GoSlice) (xs : List EntryM) (i : Nat) (e : EntryM)
    (He : xs[i]? = some e) :
    entsRO (GF := GF) s xs ⊢ ∃ (ls : List Loc) (l : Loc),
      s ↦*□ ls ∗ entRO l e ∗
      ⌜ls[i]? = some l ∧ ls.length = xs.length ∧ xs.length = sint.nat s.len ∧
        0 ≤ sint.Z s.len⌝ := by
  iintro #H
  iunfold entsRO at H
  iunfold entsPts at H
  icases H with ⟨%ls, #Hs, #Hb⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hbl := entsBig_length $$ Hb
  icases entsBig_lookup ls xs i e He $$ Hb with ⟨%l, %Hl, #Hl⟩
  iexists ls, l
  iframe Hs Hl
  ipureintro
  exact ⟨Hl, Hbl, by omega, Hlen.2⟩

/-- The slice of a read-only entry slice whose first entry is `d` is not empty. -/
theorem entsRO_cons_len (s : GoSlice) (d : EntryM) (xs : List EntryM) :
    entsRO (GF := GF) s (d :: xs) ⊢ ⌜0 < sint.Z s.len ∧ (xs.length : Int) + 1 = sint.Z s.len⌝ := by
  iintro #H
  ihave %Hl := entsPts_len $$ H
  ipureintro
  obtain ⟨h1, h2⟩ := Hl
  simp only [List.length_cons] at h1
  constructor <;> word

/-- A conf state's pointer is not `nil` (kept). -/
theorem csPts_not_null (p : Loc) (dq : DFrac) (c : ConfStateM) (al : Bool) :
    csPts (GF := GF) p dq c al ⊢ csPts p dq c al ∗ ⌜p ≠ null⌝ := by
  iintro H
  iunfold csPts at H
  icases H with ⟨%sv, %sl, %so, %sn, %pa, %Hnn, H⟩
  isplitl
  · iunfold csPts
    iexists sv, sl, so, sn, pa
    isplitr
    · ipureintro; exact Hnn
    iexact H
  · ipureintro; exact Hnn

/-- A snapshot's pointer is not `nil` (kept). -/
theorem ownSnapM_not_null (p : Loc) (dq : DFrac) (sv : SnapshotM) :
    ownSnapM (GF := GF) p dq sv ⊢ ownSnapM p dq sv ∗ ⌜p ≠ null⌝ := by
  iintro H
  iunfold ownSnapM at H
  icases H with ⟨%ds, %pm, %uf, %Hnn, H⟩
  isplitl
  · iunfold ownSnapM
    iexists ds, pm, uf
    isplitr
    · ipureintro; exact Hnn
    iexact H
  · ipureintro; exact Hnn

end lemmas

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {s : Stuckness} {E : CoPset}
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

set_option goose.wp.unfoldSliceLiterals true in
/-- `wp_slice_literal` (Perennial, `Slice.lean`) with the elements chosen by the array literal's
evaluation: a slice literal whose elements are allocated (`[]*pb.Entry{{}}`,
`NewMemoryStorage`) has elements that exist only after the allocation, so they cannot be given
before (a local copy, existential in the elements; the proof is Perennial's). -/
theorem wp_slice_literal_ex {st t : go.GoType} [IntoValTyped (GF := GF) V t]
    [st ↓u go.SliceType t] (kvs : List keyed_element) (Φ : val → IProp GF) :
    WP (App (Val (GoInstruction (CompositeLiteral (go.ArrayType (go.arrayLiteralSize kvs) t))))
          (Val (LiteralValueV kvs))) @ s; E
      {{ v, ∃ l : List V, ⌜v = #(array.mk (go.arrayLiteralSize kvs) l)⌝ ∗
        (∀ sl_ptr : Loc,
          (slice.mk sl_ptr (W64 (go.arrayLiteralSize kvs)) (W64 (go.arrayLiteralSize kvs)) ↦* l ∗
            ownSliceCap V (slice.mk sl_ptr (W64 (go.arrayLiteralSize kvs))
              (W64 (go.arrayLiteralSize kvs))) (DFrac.own 1)) -∗
          Φ #(slice.mk sl_ptr (W64 (go.arrayLiteralSize kvs)) (W64 (go.arrayLiteralSize kvs)))) }} ⊢
    WP (App (Val (GoInstruction (CompositeLiteral st))) (Val (LiteralValueV kvs))) @ s; E {{ Φ }} := by
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
    iapply HΦ
    isplitl [tmp]
    · iapply slice_array tmp_ptr _ (array.mk (go.arrayLiteralSize kvs) l) (by simp only; omega)
      iexact tmp
    · iapply ownSliceCap_empty _ rfl (by simp only; word)
  · rw [ite_eq_right hlen]; iapply wp_AngelicExit

end wps

end EtcdGrove
end Perennial

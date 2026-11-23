/-
`(*bufio.Reader).ReadByte` (see `Spec/bufio/Reader__ReadByte.lean`), with `(*Reader).fill`
(`bufio.wp_fill`). Ported from dsverify-lab's `Harness/Proof/bufio/Reader.lean`.
-/
module

public import Spec.bufio.Reader__ReadByte

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.bufio.Assumptions]

set_option goose.wp.extras true

/-- `fill()` with nothing buffered (`r = w`) and no pending error: reads into the buffer until
the underlying reader returns a byte or an error (or `io.ErrNoProgress` after 100 empty
reads). -/
theorem bufio.wp_fill (br : Loc) (ri : GoInterfaceOk) (Pre : List w8 → Nat → Prop)
    (S : List w8 → IProp GF) (E : List w8 → GoInterface → IProp GF) (R : List w8)
    (buf : GoSlice) (r lb lrs : w64) (bs : List w8)
    (hr : 0 ≤ sint.Z r ∧ sint.Z r ≤ bs.length) (hbs : 0 < bs.length)
    (hpre : bufio.preUpTo Pre bs.length) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ _root_.Perennial.io.readerOk ri Pre S E ∗ S R ∗
        br ↦ _root_.Perennial.bufio.Reader.mk buf (interface.ok ri) r r interface.nil lb lrs ∗
        buf ↦* bs }}
      (App (Val (br @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"fill"))
        (Val #()))
    {{ RET #(); ∃ (pend : List w8) (perr : GoInterface),
        ⌜pend ≠ [] ∨ perr ≠ interface.nil⌝ ∗ S (R ++ pend) ∗
        bufio.readerRep br ri Pre E R pend perr }} := by
  wp_start as ⟨#Hrd, HI, Hb, Hbuf⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hbuf
  have hl : (bs.length : Int) = sint.Z buf.len := by
    rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
  wp_auto
  wp_if_destruct
  -- `r > 0`: slide the (empty) buffered part to the front
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hr.1, Int.le_refl _, by omega⟩)]
  wp_apply wp_slice_copy_of_len_zero (V := w8) buf (slice.slice buf w8 r r) (by simp [slice.slice])
  isimp at Hb
  ihave Hb : (br ↦ _root_.Perennial.bufio.Reader.mk buf (interface.ok ri) 0 0 interface.nil lb lrs :
    IProp GF) $$ [Hb]
  · iexact Hb
  rotate_left
  -- `r = 0`
  have : r = 0 := by
    apply BitVec.eq_of_toInt_eq
    show sint.Z r = sint.Z 0
    rw [show sint.Z (0 : w64) = 0 from rfl]
    rw [show sint.Z (W64 0) = 0 from rfl] at *; omega
  subst this
  all_goals
    wp_if_destruct
    · exfalso
      have h0 : sint.Z (0 : w64) = 0 := rfl
      have h0' : sint.Z (0#64) = 0 := rfl
      (try simp only [BitVec.sub_self] at *)
      omega
    ihave #Hio := bufio.io_init_of_bufio $$ Hpkg
    ihave ⟨%enp, #Henp, %Hnp⟩ := bufio.errNoProgress_init $$ Hio
    ihave HL : (∃ (i : w64) (bs' : List w8), "i" ∷ i_ptr ↦ i ∗
        "Hb" ∷ br ↦ _root_.Perennial.bufio.Reader.mk buf (interface.ok ri) 0 0 interface.nil lb lrs ∗
        "Hbuf" ∷ buf ↦* bs' ∗ "HI" ∷ S R ∗ "%Hbs" ∷ ⌜bs'.length = bs.length⌝ : IProp GF)
      $$ [i Hb Hbuf HI]
    · iexists _, bs; iframe; ipureintro; rfl
    wp_for HL
    have h0 : sint.Z (0 : w64) = 0 := rfl
    have hbs' : (bs'.length : Int) = sint.Z buf.len := by omega
    wp_if_destruct
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Int.le_refl _, by omega, Hwf.2⟩)]
      ihave Hsl := (bufio.whole_slice buf _ bs').1 $$ Hbuf
      wp_auto
      wp_apply _root_.Perennial.io.wp_reader_Read ri Pre S E R _ bs'
        (hpre R bs'.length (by omega) (by omega)) $$ [$Hrd $HI $Hsl]
        as %n %err ⟨%data, %Hd, Hsl, HI, #Herr, %Hty⟩
      obtain ⟨hn, hdl0⟩ := Hd
      have hn' := bufio.w64_of_sintZ hn
      subst hn'
      ihave Hbuf := (bufio.whole_slice buf _ _).2 $$ Hsl
      have h63 : sint.Z buf.len < 2 ^ 63 := by word
      have hdl : data.length < 2 ^ 63 := by omega
      have hZ : sint.Z (W64 data.length) = data.length := bufio.sint_Z_W64_length hdl
      have hW0 : sint.Z (W64 0) = 0 := rfl
      wp_if_destruct
      · exfalso; omega
      have hw : sint.Z (0 + W64 data.length) = data.length := by
        simpa using hZ
      ihave #Herr' := bufio.errAt_errE E (R ++ data) err $$ Herr
      rcases err with ei | _
      · -- an error: keep it pending, return
        wp_auto
        wp_for_post
        iapply HΦ
        iexists data, interface.ok ei
        iframe HI
        isplitr
        · ipureintro; right; simp
        unfold bufio.readerRep
        iexists buf, 0, 0 + W64 data.length, lb, lrs, [], bs'.drop data.length
        simp only [List.nil_append, List.length_nil, List.length_append,
          List.length_drop]
        iframe Hb Hbuf Herr'
        ipureintro
        refine ⟨h0, by rw [hw]; simp, by omega, ?_, Hty⟩
        rw [show data.length + (bs'.length - data.length) = bs.length by omega]; exact hpre
      · wp_auto
        wp_if_destruct
        · -- a byte read: return
          wp_for_post
          iapply HΦ
          iexists data, interface.nil
          iframe HI
          isplitr
          · ipureintro; left; intro h; subst h; simp at Hif
          unfold bufio.readerRep
          iexists buf, 0, 0 + W64 data.length, lb, lrs, [], bs'.drop data.length
          simp only [List.nil_append, List.length_nil, List.length_append,
            List.length_drop]
          iframe Hb Hbuf Herr'
          ipureintro
          refine ⟨h0, by rw [hw]; simp, by omega, ?_, Hty⟩
          rw [show data.length + (bs'.length - data.length) = bs.length by omega]; exact hpre
        · -- nothing read: try again
          have hd : data = [] := by
            apply List.eq_nil_of_length_eq_zero; omega
          subst hd
          wp_for_post
          (try isimp at Hb)
          iframe
          iexists (i - W64 1), bs'
          simp only [List.append_nil, List.nil_append, List.length_nil, List.drop_zero]
          iframe HI Hbuf i
          isplitl [Hb]
          · (try isimp); iexact Hb
          ipureintro; exact Hbs
    · -- 100 empty reads: `io.ErrNoProgress`
      have hP : ¬ (sint.Z (W64 0) < sint.Z i) := by
        first | exact Hif | (intro h; apply Hif; simp [h])
      (try simp only [decide_eq_false hP, decide_true, ↓reduceIte])
      (try wp_auto)
      iapply HΦ
      iexists [], enp
      rw [List.append_nil]
      iframe HI
      isplitr
      · ipureintro; right; exact Hnp.2
      unfold bufio.readerRep
      iexists buf, 0, 0, lb, lrs, [], bs'
      simp only [List.nil_append, List.length_nil, List.append_nil]
      iframe Hb Hbuf
      isplitr
      · ipureintro
        refine ⟨h0, by simp, by omega, ?_, Hnp.1⟩
        rw [Hbs]; exact hpre
      unfold _root_.Perennial.io.errAt bufio.errE
      iright; imodintro; iright; iexact Henp

/-- See `Spec/bufio/Reader__ReadByte.lean`. -/
theorem bufio.Reader.ReadByte.wp_proof : bufio.Reader.ReadByte.spec (GF := GF) (hG := hG) := by
  intro br ri Pre S E R
  wp_start as Hown
  iunfold bufio.ownBufReader at Hown
  icases Hown with ⟨#Hpkg, #Hrd, %pend, %perr, HI, Hrep⟩
  iunfold bufio.readerRep at Hrep
  icases Hrep with ⟨%buf, %r, %w, %lb, %lrs, %pre, %post, Hb, Hbuf, %Hrw, #Herr⟩
  wp_auto
  ihave HL : (∃ (pend : List w8) (perr : GoInterface) (buf : GoSlice) (r w lb lrs : w64)
      (pre post : List w8),
      "HI" ∷ S (R ++ pend) ∗
      "Hb" ∷ br ↦ _root_.Perennial.bufio.Reader.mk buf (interface.ok ri) r w perr lb lrs ∗
      "Hbuf" ∷ buf ↦* (pre ++ pend ++ post) ∗
      "%Hrw" ∷ ⌜sint.Z r = pre.length ∧ sint.Z w = pre.length + pend.length ∧
        0 < (pre ++ pend ++ post).length ∧ bufio.preUpTo Pre (pre ++ pend ++ post).length ∧
        _root_.Perennial.io.ptrTyped perr⌝ ∗
      "#Herr" ∷ _root_.Perennial.io.errAt (bufio.errE E) (R ++ pend) perr : IProp GF)
      $$ [HI Hb Hbuf]
  · iexists pend, perr, buf, r, w, lb, _, pre, post
    iframe
    isplitr
    · ipureintro; exact Hrw
    iexact Herr
  wp_for HL
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  have h63 : sint.Z buf.len < 2 ^ 63 := by word
  have hl : ((pre ++ pend ++ post).length : Int) = sint.Z buf.len := by
    rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
  obtain ⟨Hr, Hw, Hpos, Hpre, Hty⟩ := Hrw
  have Hpre' := Hpre
  simp only [List.length_append] at hl Hpre'
  wp_if_destruct
  · -- nothing buffered
    subst Hif
    have hp : pend = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hp
    rcases perr with ep | _
    · -- a pending error: return it
      wp_auto
      wp_apply bufio.wp_readErr $$ Hb as Hb
      wp_for_post
      iapply HΦ
      iright
      rw [List.append_nil] at *
      unfold _root_.Perennial.io.errAt
      icases Herr with (%Hn | #Ha)
      · cases Hn
      iframe Ha
      isplitr
      · ipureintro; simp
      isplitr
      · ipureintro; exact Hty
      iunfold bufio.ownBufReader, bufio.readerRep
      iframe Hpkg Hrd
      iexists [], interface.nil
      simp only [List.append_nil]
      iframe HI
      iexists buf, r, r, lb, lrs, pre, post
      iframe Hbuf Hb
      isplitr
      · ipureintro; exact ⟨Hr, by simpa using Hw, Hpos, Hpre, _root_.Perennial.io.ptrTyped_nil⟩
      iapply bufio.errAt_nil'
    · wp_auto
      isimp only [List.append_nil] at HI
      wp_apply bufio.wp_fill br ri Pre S E R buf r lb lrs (pre ++ [] ++ post) (by simp at hl ⊢; omega)
        (by simp at Hpos ⊢; omega) Hpre $$ [$Hpkg $Hrd $HI $Hb $Hbuf] as ⟨%pend', %perr', -, HI, Hrep⟩
      wp_for_post
      iunfold bufio.readerRep at Hrep
      icases Hrep with ⟨%buf', %r', %w', %lb', %lrs', %pre', %post', Hb, Hbuf, %Hrw', #Herr'⟩
      iframe
      iexists pend', perr', buf', r', w', lb', lrs', pre', post'
      iframe
      isplitr
      · ipureintro; exact Hrw'
      iexact Herr'
  · -- a byte is buffered: return it
    obtain ⟨c, rest, rfl⟩ : ∃ c rest, pend = c :: rest := by
      cases pend with
      | nil =>
        exfalso; apply Hif; apply BitVec.eq_of_toInt_eq
        show sint.Z r = sint.Z w
        simp at Hw; omega
      | cons c rest => exact ⟨c, rest, rfl⟩
    simp only [List.length_cons] at hl
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
    wp_apply wp_load_slice_index buf (sint.Z r) (pre ++ c :: rest ++ post) _ c (by omega)
      $$ [$Hbuf] as Hbuf
    · ipureintro
      rw [Hr]
      simp
    have hr1 : sint.Z (r + W64 1) = (pre ++ [c]).length := by
      simp only [List.length_append, List.length_singleton]
      have : sint.Z (W64 1) = 1 := rfl
      word
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iunfold bufio.ownBufReader, bufio.readerRep
    iframe Hpkg Hrd
    iexists rest, perr
    rw [show R ++ [c] ++ rest = R ++ c :: rest by simp]
    iframe HI
    iexists buf, r + W64 1, w, W64 (uint.Z c), lrs, pre ++ [c], post
    rw [show pre ++ [c] ++ rest ++ post = pre ++ c :: rest ++ post by simp]
    iframe Hbuf Hb Herr
    ipureintro
    refine ⟨hr1, ?_, Hpos, Hpre, Hty⟩
    · simp at Hw ⊢; omega

end proof

end EtcdGrove
end Perennial

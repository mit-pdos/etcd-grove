/-
`(*bufio.Reader).Read`'s generic spec (see `Spec/bufio/Reader__ReadOk.lean`). Ported from
dsverify-lab's `Harness/Proof/bufio/Reader.lean` (`wp_Read`).
-/
module

public import Spec.bufio.Reader__ReadOk

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

theorem bufio.Reader.Read.wp_proofOk : bufio.Reader.Read.specOk (GF := GF) (hG := hG) := by
  intro br ri Pre S E R p ps hpre
  wp_start as ⟨Hown, Hp⟩
  iunfold bufio.ownBufReader at Hown
  icases Hown with ⟨#Hpkg, #Hrd, %pend, %perr, HI, Hrep⟩
  iunfold bufio.readerRep at Hrep
  icases Hrep with ⟨%buf, %r, %w, %lb, %lrs, %pre, %post, Hb, Hbuf, %Hrw, #Herr⟩
  obtain ⟨Hr, Hw, Hpos, Hpre, Hty⟩ := Hrw
  ihave %Hplen := ownSlice_len _ _ _ $$ Hp
  ihave %Hlen := ownSlice_len _ _ _ $$ Hbuf
  have h63 : sint.Z buf.len < 2 ^ 63 := by word
  have hl : ((pre ++ pend ++ post).length : Int) = sint.Z buf.len := by
    rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
  have hpl : (ps.length : Int) = sint.Z p.len := by
    rw [Hplen.1]; exact Int.toNat_of_nonneg Hplen.2
  have hp63 : sint.Z p.len < 2 ^ 63 := by word
  have Hpre' := Hpre
  simp only [List.length_append] at hl Hpre'
  wp_auto
  wp_if_destruct
  · -- `len(p) = 0`
    have hps : ps = [] := List.eq_nil_of_length_eq_zero (by
      have : sint.Z p.len = 0 := by rw [Hif]; rfl
      omega)
    subst hps
    wp_apply bufio.wp_Buffered $$ Hb as Hb
    wp_if_destruct
    · iapply HΦ
      iexists []
      simp only [List.append_nil, List.length_nil, List.drop_nil]
      iframe Hp
      isplitr
      · ipureintro; exact ⟨rfl, Nat.le_refl _⟩
      isplitl
      · iunfold bufio.ownBufReader, bufio.readerRep
        iframe Hpkg Hrd
        iexists pend, perr
        iframe HI
        iexists buf, r, w, lb, lrs, pre, post
        iframe Hb Hbuf Herr
        ipureintro; exact ⟨Hr, Hw, Hpos, Hpre, Hty⟩
      isplitl
      · iapply bufio.errAt_nil'
      ipureintro; exact _root_.Perennial.io.ptrTyped_nil
    · -- nothing buffered: the pending error
      have hp : pend = [] := List.eq_nil_of_length_eq_zero (by
        have hwr : sint.Z (w - r) = pend.length := by word
        have h0 : sint.Z (W64 0) = 0 := rfl
        omega)
      subst hp
      wp_apply bufio.wp_readErr $$ Hb as Hb
      iapply HΦ
      iexists []
      simp only [List.append_nil, List.length_nil, List.drop_nil]
      iframe Hp Herr
      isplitr
      · ipureintro; exact ⟨rfl, Nat.le_refl _⟩
      isplitl
      · iunfold bufio.ownBufReader, bufio.readerRep
        iframe Hpkg Hrd
        iexists [], interface.nil
        simp only [List.append_nil]
        iframe HI
        iexists buf, r, w, lb, lrs, pre, post
        iframe Hb Hbuf
        isplitr
        · ipureintro
          exact ⟨Hr, by simpa using Hw, by simpa using Hpos, by simpa using Hpre,
            _root_.Perennial.io.ptrTyped_nil⟩
        iapply bufio.errAt_nil'
      ipureintro; exact Hty
  have hps : ps ≠ [] := by
    intro h; subst h; apply Hif; apply BitVec.eq_of_toInt_eq
    show sint.Z p.len = sint.Z (W64 0)
    simp at hpl; rw [← hpl]; rfl
  have hpsl : 0 < ps.length := List.length_pos_iff.mpr hps
  wp_if_destruct
  -- nothing buffered
  subst Hif
  have hp : pend = [] := List.eq_nil_of_length_eq_zero (by omega)
  subst hp
  simp only [List.append_nil] at Hpos Hpre Hw
  isimp only [List.append_nil] at HI Herr Hbuf
  rcases perr with ep | _
  · -- a pending error: return it
    wp_auto
    wp_apply bufio.wp_readErr $$ Hb as Hb
    iapply HΦ
    iexists []
    simp only [List.append_nil, List.nil_append, List.length_nil, List.drop_zero]
    iframe Hp Herr
    isplitr
    · ipureintro; exact ⟨rfl, Nat.zero_le _⟩
    isplitl
    · iunfold bufio.ownBufReader, bufio.readerRep
      iframe Hpkg Hrd
      iexists [], interface.nil
      simp only [List.append_nil]
      iframe HI
      iexists buf, r, r, lb, lrs, pre, post
      iframe Hb Hbuf
      isplitr
      · ipureintro; exact ⟨Hr, Hr, Hpos, Hpre, _root_.Perennial.io.ptrTyped_nil⟩
      iapply bufio.errAt_nil'
    ipureintro; exact Hty
  wp_auto
  wp_if_destruct
  · -- a large read: straight into `p`
    wp_apply _root_.Perennial.io.wp_reader_Read ri Pre S E R p ps (hpre R hpsl) $$ [$Hrd $HI $Hp]
      as %n %err ⟨%data, %Hd, Hp, HI, #Herr2, %Hty2⟩
    obtain ⟨hn, Hd⟩ := Hd
    have hn' := bufio.w64_of_sintZ hn
    subst hn'
    ihave #Herr2' := bufio.errAt_errE E (R ++ data) err $$ Herr2
    isimp at Hb
    have hdl : data.length < 2 ^ 63 := by omega
    have hZ : sint.Z (W64 data.length) = data.length := bufio.sint_Z_W64_length hdl
    have hW0 : sint.Z (W64 0) = 0 := rfl
    wp_if_destruct
    · exfalso; omega
    wp_if_destruct
    · -- `n > 0`: `lastByte = p[n-1]`
      have hpos : 0 < data.length := by omega
      have hi : sint.Z (W64 data.length - W64 1) = data.length - 1 := by
        have : sint.Z (W64 1) = 1 := rfl
        word
      have hpl' : ((data ++ ps.drop data.length).length : Int) = sint.Z p.len := by
        simp; omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
      wp_apply wp_load_slice_index p (sint.Z (W64 data.length - W64 1)) _ _
        (data[data.length - 1]'(by omega)) (by omega) $$ [$Hp] as Hp
      · ipureintro
        rw [hi, show ((data.length : Int) - 1).toNat = data.length - 1 by omega,
          List.getElem?_append_left (by omega)]
        simp
      wp_apply bufio.wp_readErr $$ Hb as Hb
      iapply HΦ
      iexists data
      iframe Hp Herr2'
      isplitr
      · ipureintro; exact ⟨hZ, Hd⟩
      isplitl
      · iunfold bufio.ownBufReader, bufio.readerRep
        iframe Hpkg Hrd
        iexists [], interface.nil
        simp only [List.append_nil]
        iframe HI
        iexists buf, r, r, _, _, pre, post
        iframe Hb Hbuf
        isplitr
        · ipureintro; exact ⟨Hr, Hr, Hpos, Hpre, _root_.Perennial.io.ptrTyped_nil⟩
        iapply bufio.errAt_nil'
      ipureintro; exact Hty2
    · wp_apply bufio.wp_readErr $$ Hb as Hb
      iapply HΦ
      iexists data
      iframe Hp Herr2'
      isplitr
      · ipureintro; exact ⟨hZ, Hd⟩
      isplitl
      · iunfold bufio.ownBufReader, bufio.readerRep
        iframe Hpkg Hrd
        iexists [], interface.nil
        simp only [List.append_nil]
        iframe HI
        iexists buf, r, r, _, _, pre, post
        iframe Hb Hbuf
        isplitr
        · ipureintro; exact ⟨Hr, Hr, Hpos, Hpre, _root_.Perennial.io.ptrTyped_nil⟩
        iapply bufio.errAt_nil'
      ipureintro; exact Hty2
  -- one read into the buffer, then copy
  wp_apply _root_.Perennial.io.wp_reader_Read ri Pre S E R buf (pre ++ post)
    (Hpre R _ (by simp at Hpos ⊢; omega) (by simp)) $$ [$Hrd $HI $Hbuf]
    as %n %err ⟨%data, %Hd, Hbuf, HI, #Herr2, %Hty2⟩
  obtain ⟨hn, Hd⟩ := Hd
  have hn' := bufio.w64_of_sintZ hn
  subst hn'
  ihave #Herr2' := bufio.errAt_errE E (R ++ data) err $$ Herr2
  isimp at Hb
  simp only [List.length_append] at Hd hl
  have hdl : data.length < 2 ^ 63 := by omega
  have hZ : sint.Z (W64 data.length) = data.length := bufio.sint_Z_W64_length hdl
  have hW0 : sint.Z (W64 0) = 0 := rfl
  wp_if_destruct
  · exfalso; omega
  wp_if_destruct
  · -- nothing read
    have hd : data = [] := List.eq_nil_of_length_eq_zero (by
      have := congrArg (fun x : w64 => sint.Z x) Hif; omega)
    subst hd
    wp_apply bufio.wp_readErr $$ Hb as Hb
    iapply HΦ
    iexists []
    simp only [List.nil_append, List.length_nil, List.drop_zero]
    iframe Hp Herr2'
    isplitr
    · ipureintro; exact ⟨rfl, Nat.zero_le _⟩
    isplitl
    · iunfold bufio.ownBufReader, bufio.readerRep
      iframe Hpkg Hrd
      iexists [], interface.nil
      simp only [List.append_nil]
      iframe HI
      iexists buf, _, _, _, _, [], pre ++ post
      simp only [List.nil_append]
      iframe Hb Hbuf
      isplitr
      · ipureintro
        refine ⟨rfl, rfl, by simp at Hpos ⊢; omega, ?_, _root_.Perennial.io.ptrTyped_nil⟩
        simpa using Hpre
      iapply bufio.errAt_nil'
    ipureintro; exact Hty2
  -- something read: the common state
  have hne : data ≠ [] := by
    intro h; subst h; exact Hif rfl
  generalize hw0 : (0#64 + W64 data.length : w64) = w0
  generalize hr0 : (0#64 : w64) = r0
  ihave Hst : (∃ (pend : List w8) (perr : GoInterface) (r w : w64) (pre post : List w8),
      "HI" ∷ S (R ++ pend) ∗
      "Hb" ∷ br ↦ _root_.Perennial.bufio.Reader.mk buf (interface.ok ri) r w perr lb lrs ∗
      "Hbuf" ∷ buf ↦* (pre ++ pend ++ post) ∗
      "%Hrw" ∷ ⌜sint.Z r = pre.length ∧ sint.Z w = pre.length + pend.length ∧
        0 < (pre ++ pend ++ post).length ∧ bufio.preUpTo Pre (pre ++ pend ++ post).length ∧
        _root_.Perennial.io.ptrTyped perr ∧ pend ≠ [] ∧ r = r0 ∧ w = w0⌝ ∗
      "#Herr" ∷ _root_.Perennial.io.errAt (bufio.errE E) (R ++ pend) perr : IProp GF)
    $$ [HI Hb Hbuf]
  · iexists data, err, r0, w0, [], (pre ++ post).drop data.length
    simp only [List.nil_append]
    iframe HI Hb Hbuf Herr2'
    ipureintro
    have hlen' : (data ++ List.drop data.length (pre ++ post)).length = (pre ++ post).length := by
      simp only [List.length_append, List.length_drop] at Hd ⊢; omega
    refine ⟨?_, ?_, ?_, ?_, Hty2, hne, ?_⟩
    · subst hr0; rfl
    · subst hw0; simpa using hZ
    · rw [hlen']; simp at Hpos ⊢; omega
    · rw [hlen']; simpa using Hpre
    · simp
  clear Hif Hd hZ hdl hl hne hw0 hr0 Hr Hw Hpos Hpre Hpre' Hty
  icases Hst with ⟨%pend, %perr, %r, %w, %pre, %post, HI, Hb, Hbuf, %Hrw, #Herr⟩
  obtain ⟨h1, h2, h3, h3', h3'', h4, h5, h6⟩ := Hrw
  subst r0 w0
  have Hr := h1
  have Hw := h2
  have Hpos := h3
  have Hpre := h3'
  have Hty := h3''
  have hne' := h4
  clear h1 h2 h3 h3' h3'' h4
  rotate_left
  -- something buffered: the common state
  have hne' : pend ≠ [] := by
    intro h; subst h; apply Hif; apply BitVec.eq_of_toInt_eq
    show sint.Z r = sint.Z w
    simp at Hw; omega
  all_goals
    ihave %Hlen2 := ownSlice_len _ _ _ $$ Hbuf
    ihave %Hwf2 := ownSlice_wf _ _ _ $$ Hbuf
    have hl2 : ((pre ++ pend ++ post).length : Int) = sint.Z buf.len := by
      rw [Hlen2.1]; exact Int.toNat_of_nonneg Hlen2.2
    simp only [List.length_append] at hl2
    have hpos : 0 < pend.length := List.length_pos_iff.mpr hne'
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega, by omega⟩)]
    ihave ⟨Hsub, Hback⟩ := bufio.ownSlice_sub_acc (V := w8) r w buf (DFrac.own 1)
      (pre ++ pend ++ post) ⟨by omega, by omega, by omega⟩ $$ Hbuf
    have hsub : subslice (sint.nat r) (sint.nat w) (pre ++ pend ++ post) = pend := by
      rw [subslice_def, show sint.nat w = (pre ++ pend).length by
          show (sint.Z w).toNat = _; simp; omega, List.append_assoc, ← List.append_assoc pre,
        List.take_left, show sint.nat r = pre.length by show (sint.Z r).toNat = _; omega,
        List.drop_left]
    rw [hsub]
    wp_apply wp_slice_copy_int (V := w8) p ps (slice.slice buf w8 r w) pend (DFrac.own 1)
      $$ [$Hp $Hsub] as %n ⟨%Hn, Hp, Hsub⟩
    ihave Hbuf := Hback $$ Hsub
    have hk : sint.Z n = (min ps.length pend.length : Nat) := by
      rw [Hn]
    have hrn : sint.Z (r + n - W64 1) = pre.length + (min ps.length pend.length : Nat) - 1 := by
      have : sint.Z (W64 1) = 1 := rfl
      word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
    wp_apply wp_load_slice_index buf (sint.Z (r + n - W64 1)) _ _
      (pend[min ps.length pend.length - 1]'(by omega)) (by omega) $$ [$Hbuf] as Hbuf
    · ipureintro
      rw [hrn, show ((pre.length : Int) + (min ps.length pend.length : Nat) - 1).toNat =
          pre.length + (min ps.length pend.length - 1) by omega, List.append_assoc,
        List.getElem?_append_right (by omega), List.getElem?_append_left (by omega)]
      simp
    isimp at Hb
    iapply HΦ
    iexists pend.take ps.length
    have hdl : (pend.take ps.length).length = min ps.length pend.length := List.length_take
    have hdrop : ps.drop pend.length = ps.drop (pend.take ps.length).length := by
      rw [hdl]
      by_cases h : pend.length ≤ ps.length
      · rw [Nat.min_eq_right h]
      · rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
    rw [← hdrop]
    iframe Hp
    isplitr
    · ipureintro
      refine ⟨?_, by omega⟩
      rw [hk, hdl]
    isplitl
    · iunfold bufio.ownBufReader, bufio.readerRep
      iframe Hpkg Hrd
      iexists pend.drop ps.length, perr
      rw [List.append_assoc R, List.take_append_drop]
      iframe HI
      iexists buf, r + n, w, _, _, pre ++ pend.take ps.length, post
      rw [show pre ++ pend.take ps.length ++ pend.drop ps.length ++ post = pre ++ pend ++ post by
        rw [List.append_assoc pre, List.take_append_drop]]
      iframe Hb Hbuf Herr
      ipureintro
      refine ⟨?_, ?_, Hpos, Hpre, Hty⟩
      · simp only [List.length_append, hdl]; word
      · simp only [List.length_append, List.length_drop, hdl] at hl2 ⊢
        omega
    isplitl
    · iapply bufio.errAt_nil'
    ipureintro; exact _root_.Perennial.io.ptrTyped_nil

end proof

end EtcdGrove
end Perennial

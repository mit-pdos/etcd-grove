/-
`(*bufio.Reader).Peek` (see `Spec/bufio/Reader__Peek.lean`).
-/
module

public import Spec.bufio.Reader__Peek
public import Spec.bufio.Reader__fill

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

/-- `b.readErr()`: the pending error, cleared. -/
theorem bufio.wp_readErr_pk (b : Loc) (v : _root_.Perennial.bufio.Reader) :
    {{ (b ↦ v : IProp GF) }}
      (App (Val (b @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"readErr"))
        (Val #()))
    {{ RET #v.err'; b ↦ { v with err' := GoInterface.nil } }} := by
  wp_start as Hv
  try wp_auto
  iapply HΦ
  iexact Hv

theorem bufio.eq_of_sub_lt_one (r w : w64) (h0 : 0 ≤ sint.Z r) (h1 : sint.Z r ≤ sint.Z w)
    (h : sint.Z (w - r) < sint.Z (W64 1)) : r = w := by word

theorem bufio.sub_lt_len (r w l : w64) (h0 : 0 ≤ sint.Z r) (h1 : sint.Z r ≤ sint.Z w)
    (h : sint.Z (w - r) < sint.Z (W64 1)) (hl : 0 < sint.Z l) : sint.Z (w - r) < sint.Z l := by word

theorem bufio.add_sub_self (a : w64) : a + (a - a) = a := by word

theorem bufio.len_pos (l : w64) (n : Nat) (hn : n = sint.nat l) (h0 : 0 ≤ sint.Z l) (hp : 0 < n) :
    0 < sint.Z l := by subst hn; word

theorem bufio.sZ_add_one_pk (a c : w64) (h0 : 0 ≤ sint.Z a) (h : sint.Z a < sint.Z c) :
    sint.Z (a + W64 1) = sint.Z a + 1 := by word

theorem bufio.nat_add_one_pk (a c : w64) (h0 : 0 ≤ sint.Z a) (h : sint.Z a < sint.Z c) :
    sint.nat (a + W64 1) = sint.nat a + 1 := by word

theorem bufio.lt_of_sub_ge_one (r w : w64) (h0 : 0 ≤ sint.Z r) (h1 : sint.Z r ≤ sint.Z w)
    (h : ¬ sint.Z (w - r) < sint.Z (W64 1)) : sint.Z r < sint.Z w := by word

theorem bufio.sZ_toNat_pk (a : w64) : (sint.Z a).toNat = sint.nat a := rfl

theorem bufio.sZ_le_of_nat_pk (w l : w64) (n : Nat) (h : sint.nat w ≤ n) (hn : n = sint.nat l)
    (h0 : 0 ≤ sint.Z l) (hw : 0 ≤ sint.Z w) : sint.Z w ≤ sint.Z l := by subst hn; word

theorem bufio.Reader.Peek.wp_proof (wp_fill : bufio.Reader.fill.spec (GF := GF) (hG := hG)) :
    bufio.Reader.Peek.spec (GF := GF) (hG := hG) := by
  intro b ri S E r
  iintro #Hrd #HSb
  wp_start as Hb
  iunfold bufio.ownReader at Hb
  icases Hb with ⟨#Hpkg, %v, %bs, Hv, Hbuf, %Hwf, HS, #Herr⟩
  try wp_auto
  ihave Hinv : (∃ q e, bufio.ownReaderBuf b ri S E r q e) $$ [Hv Hbuf HS]
  · iexists _, _
    iunfold bufio.ownReaderBuf
    iframe Hpkg
    iexists _, bs
    iframe Hv Hbuf
    iframe HS Herr
    ipureintro
    exact ⟨Hwf.1, Hwf.2.1, Hwf.2.2.1, Hwf.2.2.2.1, Hwf.2.2.2.2.1, Hwf.2.2.2.2.2, rfl, rfl⟩
  iclear Herr
  clear Hwf
  wp_for
  icases Hinv with ⟨%q, %e, Hinv⟩
  iunfold bufio.ownReaderBuf at Hinv
  icases Hinv with ⟨-, %v, %bs, Hv, Hbuf, %Hwf, HS, #Herr⟩
  ihave %Hblen := ownSlice_len _ _ _ $$ Hbuf
  ihave %Hbwf := ownSlice_wf v.buf' _ bs $$ Hbuf
  try wp_auto
  have hlen0 : 0 < sint.Z v.buf'.len := bufio.len_pos _ _ Hblen.1 Hblen.2 Hwf.2.2.2.2.1
  wp_if_destruct
  · have hlt1 := Hif
    have hrw : v.r' = v.w' := bufio.eq_of_sub_lt_one _ _ Hwf.2.1 Hwf.2.2.1 hlt1
    wp_if_destruct
    · rcases hve : v.err' with e' | _
      · simp only []
        try wp_auto
        have hft : (#false : val) ≠ #true := fun h => by have := go.intoVal_inj h; simp at this
        simp only [decide_eq_true_eq, ite_eq_right hft, ite_true]
        try wp_auto
        wp_if_destruct
        · exfalso; have : sint.Z (W64 1) = 1 := by decide
          omega
        try wp_auto
        wp_if_destruct
        · try wp_auto
          wp_apply (bufio.wp_readErr_pk b _) $$ Hv as Hv
          try wp_auto
          rw [hve]
          try wp_auto
          have hq : q = [] := by rw [← Hwf.2.2.2.2.2.2.1, hrw]; simp [subslice]
          subst hq
          have he : e = GoInterface.ok e' := Hwf.2.2.2.2.2.2.2.symm.trans hve
          subst he
          rw [show v.r' + (v.w' - v.r') = v.r' by rw [← hrw]; exact bufio.add_sub_self _]
          rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z v.r' ∧ sint.Z v.r' ≤ sint.Z v.r' ∧
              sint.Z v.r' ≤ sint.Z v.buf'.cap from ⟨Hwf.2.1, Int.le_refl _, by
                have := bufio.sZ_le_of_nat_pk _ _ _ Hwf.2.2.2.1 Hblen.1 Hblen.2 (by omega)
                rw [hrw]; have := Hbwf.2; omega⟩))]
          try wp_auto
          iapply HΦ
          iright
          isplitr
          · ipureintro; simp
          isplitr
          · iapply (io.errAt_eq (List.append_nil r)); iexact Herr
          iunfold bufio.ownReader
          iframe Hpkg
          iexists { v with err' := GoInterface.nil }, bs
          iframe Hv Hbuf
          simp only []
          rw [Hwf.2.2.2.2.2.2.1]
          iframe HS
          isplitr
          · ipureintro
            exact ⟨Hwf.1, Hwf.2.1, Hwf.2.2.1, Hwf.2.2.2.1, Hwf.2.2.2.2.1, Hwf.2.2.2.2.2.1⟩
          iapply io.errAt_nil
        · exfalso; exact Hif hlt1
      · simp only []
        try wp_auto
        simp only [_root_.decide_true, ite_true]
        try wp_auto
        ihave Hf := wp_fill b ri S E r $$ Hrd HSb
        have hq : q = [] := by rw [← Hwf.2.2.2.2.2.2.1, hrw]; simp [subslice]
        subst hq
        wp_apply Hf $$ [Hv Hbuf HS] as ⟨%ys, %e2, %Hne, Hb2⟩
        · iunfold bufio.ownReaderBuf
          iframe Hpkg
          iexists v, bs
          iframe Hv Hbuf HS
          isplitr
          · ipureintro
            exact ⟨Hwf.1, Hwf.2.1, Hwf.2.2.1, Hwf.2.2.2.1, Hwf.2.2.2.2.1, Hwf.2.2.2.2.2.1,
              Hwf.2.2.2.2.2.2.1, hve⟩
          iapply io.errAt_nil
        wp_for_post
        iframe
        iexists ys, e2
        iexact Hb2
    · exact absurd (bufio.sub_lt_len _ _ _ Hwf.2.1 Hwf.2.2.1 hlt1 hlen0) Hif
  · try wp_auto
    have hlt : sint.Z v.r' < sint.Z v.w' := bufio.lt_of_sub_ge_one _ _ Hwf.2.1 Hwf.2.2.1 Hif
    have hwl : sint.Z v.w' ≤ sint.Z v.buf'.len :=
      bufio.sZ_le_of_nat_pk _ _ _ Hwf.2.2.2.1 Hblen.1 Hblen.2 (by omega)
    have hr1 := bufio.sZ_add_one_pk _ _ Hwf.2.1 hlt
    have hn1 := bufio.nat_add_one_pk _ _ Hwf.2.1 hlt
    have hge1 := Hif
    wp_if_destruct
    · exfalso; have : sint.Z (W64 1) = 1 := by decide
      omega
    try wp_auto
    wp_if_destruct
    · exact absurd Hif hge1
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z v.r' ∧ sint.Z v.r' ≤ sint.Z (v.r' + W64 1) ∧
        sint.Z (v.r' + W64 1) ≤ sint.Z v.buf'.cap from ⟨Hwf.2.1, by omega, by have := Hbwf.2; omega⟩))]
    try wp_auto
    have hb : 0 ≤ sint.Z v.r' ∧ sint.Z v.r' ≤ sint.Z (v.r' + W64 1) ∧
        sint.Z (v.r' + W64 1) ≤ sint.Z v.buf'.len := ⟨Hwf.2.1, by omega, by omega⟩
    have hrl : sint.nat v.r' < bs.length := by
      have h1 : sint.nat v.r' < sint.nat v.w' := by
        rw [← bufio.sZ_toNat_pk, ← bufio.sZ_toNat_pk]; omega
      have := Hwf.2.2.2.1; omega
    have hmid : subslice (sint.nat v.r') (sint.nat (v.r' + W64 1)) bs = [bs[sint.nat v.r']] := by
      rw [hn1]; simp only [subslice]
      rw [List.drop_eq_getElem_cons (by rw [List.length_take]; omega)]
      simp [List.getElem_take]
    have hq : q = bs[sint.nat v.r'] :: subslice (sint.nat (v.r' + W64 1)) (sint.nat v.w') bs := by
      rw [← Hwf.2.2.2.2.2.2.1, hn1]
      have hn2 : sint.nat v.r' < sint.nat v.w' := by
        rw [← bufio.sZ_toNat_pk, ← bufio.sZ_toNat_pk]; omega
      have := Hwf.2.2.2.1
      simp only [subslice]
      rw [List.drop_eq_getElem_cons (by rw [List.length_take]; omega)]
      simp [List.getElem_take, Nat.add_comm]
    icases (ownSlice_slice v.r' (v.r' + W64 1) v.buf' (DFrac.own 1) bs hb).mp $$ Hbuf
      with ⟨Hb0, Hbm, Hb1⟩
    rw [hmid]
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists bs[sint.nat v.r'], subslice (sint.nat (v.r' + W64 1)) (sint.nat v.w') bs, e
    iframe Hbm
    iintro Hbm
    rw [← hmid]
    ihave Hbuf := (ownSlice_slice v.r' (v.r' + W64 1) v.buf' (DFrac.own 1) bs hb).mpr $$ [Hb0 Hbm Hb1]
    · iframe
    rw [← hq]
    iunfold bufio.ownReaderBuf
    iframe Hpkg
    iexists v, bs
    iframe Hv Hbuf HS Herr
    ipureintro; exact Hwf

end proof

end EtcdGrove
end Perennial

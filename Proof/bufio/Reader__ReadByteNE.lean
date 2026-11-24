/-
`(*bufio.Reader).ReadByte` (see `Spec/bufio/Reader__ReadByte.lean`).
-/
module

public import Spec.bufio.Reader__ReadByteNE
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
theorem bufio.wp_readErr_rb (b : Loc) (v : _root_.Perennial.bufio.Reader) :
    {{ (b ↦ v : IProp GF) }}
      (App (Val (b @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"readErr"))
        (Val #()))
    {{ RET #v.err'; b ↦ { v with err' := GoInterface.nil } }} := by
  wp_start as Hv
  try wp_auto
  iapply HΦ
  iexact Hv

theorem bufio.w64_eq_of_sZ (a c : w64) (h : sint.Z a = sint.Z c) : a = c := by word

theorem bufio.sZ_le_of_nat (w l : w64) (n : Nat) (h : sint.nat w ≤ n) (hn : n = sint.nat l)
    (h0 : 0 ≤ sint.Z l) (hw : 0 ≤ sint.Z w) : sint.Z w ≤ sint.Z l := by subst hn; word

theorem bufio.nat_lt_of_sZ (a c : w64) (h0 : 0 ≤ sint.Z a) (h : sint.Z a < sint.Z c) :
    sint.nat a < sint.nat c := by word

theorem bufio.nat_add_one (a c : w64) (h0 : 0 ≤ sint.Z a) (h : sint.Z a < sint.Z c) :
    sint.nat (a + W64 1) = sint.nat a + 1 := by word

theorem bufio.sZ_add_one (a c : w64) (h0 : 0 ≤ sint.Z a) (h : sint.Z a < sint.Z c) :
    sint.Z (a + W64 1) = sint.Z a + 1 := by word

theorem bufio.sZ_toNat (a : w64) : (sint.Z a).toNat = sint.nat a := rfl

theorem bufio.Reader.ReadByte.wp_proofNE (wp_fill : bufio.Reader.fill.spec (GF := GF) (hG := hG)) :
    bufio.Reader.ReadByte.specNE (GF := GF) (hG := hG) := by
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
  try wp_auto
  wp_if_destruct
  · have hrw : v.r' = v.w' := by simpa using go.intoVal_inj Hif
    have hq : q = [] := by rw [← Hwf.2.2.2.2.2.2.1, hrw]; simp [subslice]
    subst hq
    rcases hve : v.err' with e' | _
    · simp only []
      try wp_auto
      wp_apply (bufio.wp_readErr_rb b v) $$ Hv as Hv
      try wp_auto
      wp_for_post
      iapply HΦ
      iright
      rw [hve]
      have he : e = GoInterface.ok e' := Hwf.2.2.2.2.2.2.2.symm.trans hve
      subst he
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
    · simp only []
      try wp_auto
      ihave Hf := wp_fill b ri S E r $$ Hrd HSb
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
  · have hrw : v.r' ≠ v.w' := by
      intro h; apply Hif; simp [h]
    rw [decide_eq_false hrw]
    simp only [Bool.false_eq_true, ite_false]
    try wp_auto
    have hlt : sint.Z v.r' < sint.Z v.w' := by
      have : sint.Z v.r' ≠ sint.Z v.w' := fun h => hrw (bufio.w64_eq_of_sZ _ _ h)
      have := Hwf.2.2.1; omega
    have hwlen : sint.Z v.w' ≤ sint.Z v.buf'.len := by
      exact bufio.sZ_le_of_nat _ _ _ Hwf.2.2.2.1 Hblen.1 Hblen.2 (by omega)
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z v.r' ∧ sint.Z v.r' < sint.Z v.buf'.len
      from ⟨Hwf.2.1, by omega⟩))]
    have hrl : (sint.Z v.r').toNat < bs.length := by
      rw [bufio.sZ_toNat]
      have := bufio.nat_lt_of_sZ _ _ Hwf.2.1 hlt
      have := Hwf.2.2.2.1; omega
    obtain ⟨x, hx⟩ : ∃ x, bs[(sint.Z v.r').toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem hrl⟩
    wp_apply (wp_load_slice_index v.buf' _ bs (DFrac.own 1) x Hwf.2.1) $$ [Hbuf] as Hbuf
    · iframe; ipureintro; exact hx
    try wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    have hq : q = x :: subslice (sint.nat (v.r' + W64 1)) (sint.nat v.w') bs := by
      rw [← Hwf.2.2.2.2.2.2.1]
      have hn : sint.nat (v.r' + W64 1) = sint.nat v.r' + 1 := bufio.nat_add_one _ _ Hwf.2.1 hlt
      rw [hn]
      simp only [subslice]
      have hn1 : sint.nat v.r' < sint.nat v.w' := bufio.nat_lt_of_sZ _ _ Hwf.2.1 hlt
      have hn2 : sint.nat v.w' ≤ bs.length := Hwf.2.2.2.1
      rw [List.drop_eq_getElem_cons (by rw [List.length_take]; omega)]
      congr 1
      simp only [List.getElem_take]
      have h2 : bs[sint.nat v.r']? = some x := hx
      rw [← bufio.sZ_toNat] at h2
      rw [List.getElem?_eq_getElem hrl] at h2
      exact Option.some.inj h2
    have hr2 : r ++ q = (r ++ [x]) ++ subslice (sint.nat (v.r' + W64 1)) (sint.nat v.w') bs := by
      rw [hq]; simp
    iunfold bufio.ownReader
    iframe Hpkg
    iexists _, bs
    iframe Hv Hbuf
    simp only []
    rw [← hr2]
    iframe HS
    isplitr
    · ipureintro
      have h1 := bufio.sZ_add_one _ _ Hwf.2.1 hlt
      exact ⟨Hwf.1, by omega, by omega, Hwf.2.2.2.1, Hwf.2.2.2.2.1, Hwf.2.2.2.2.2.1⟩
    rw [Hwf.2.2.2.2.2.2.2]
    iexact Herr

end proof

end EtcdGrove
end Perennial

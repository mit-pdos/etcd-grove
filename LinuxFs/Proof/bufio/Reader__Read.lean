/-
`(*bufio.Reader).Read` (see `LinuxFs/Spec/bufio/Reader__Read.lean`).
-/
module

public import LinuxFs.Spec.bufio.Reader__Read

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
theorem bufio.wp_readErr (b : Loc) (v : _root_.Perennial.bufio.Reader) :
    {{ (b ↦ v : IProp GF) }}
      (App (Val (b @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"readErr"))
        (Val #()))
    {{ RET #v.err'; b ↦ { v with err' := GoInterface.nil } }} := by
  wp_start as Hv
  try wp_auto
  iapply HΦ
  iexact Hv

/-- `b.Buffered()`: `w - r`. -/
theorem bufio.wp_Buffered (b : Loc) (v : _root_.Perennial.bufio.Reader) :
    {{ (b ↦ v : IProp GF) }}
      (App (Val (b @!! go.GoType.PointerType _root_.Perennial.bufio.Reader.ty @!! go!"Buffered"))
        (Val #()))
    {{ RET #(v.w' - v.r'); b ↦ v }} := by
  wp_start as Hv
  try wp_auto
  iapply HΦ
  iexact Hv

/-- `copy`'s result on the destination, as the copied prefix `ys` and the rest. -/
theorem bufio.copy_list {α : Type} (xs sub : List α) :
    sub.take xs.length ++ xs.drop sub.length =
      sub.take (min xs.length sub.length) ++
        xs.drop (sub.take (min xs.length sub.length)).length := by
  rcases Nat.le_total xs.length sub.length with h | h
  · rw [Nat.min_eq_left h, List.length_take, Nat.min_eq_left h, List.drop_of_length_le h,
      List.drop_length]
  · rw [Nat.min_eq_right h, List.take_of_length_le h, List.take_length]

theorem bufio.subslice_length {α : Type} (a b : Nat) (l : List α) (h : b ≤ l.length) :
    (subslice a b l).length = b - a := by
  simp only [subslice, List.length_drop, List.length_take]; omega

theorem bufio.length_append_drop {α : Type} (ys l : List α) (h : ys.length ≤ l.length) :
    (ys ++ l.drop ys.length).length = l.length := by
  simp only [List.length_append, List.length_drop]; omega

theorem bufio.subslice_prefix {α : Type} (ys l : List α) :
    subslice 0 ys.length (ys ++ l) = ys := by
  simp [subslice]

/-- Delivering the first `k` buffered bytes. -/
theorem bufio.subslice_take_split {α : Type} (a b k : Nat) (l : List α) :
    subslice a b l = (subslice a b l).take k ++ subslice (a + k) b l := by
  simp only [subslice]
  rw [show (l.take b).drop (a + k) = ((l.take b).drop a).drop k by rw [List.drop_drop]]
  exact (List.take_append_drop _ _).symm

/-- Re-establish `bufio.ownReader` from its parts. -/
theorem bufio.ownReader_intro (b : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → Prop) (r : List w8) (v : _root_.Perennial.bufio.Reader)
    (bs : List w8)
    (Hwf : v.rd' = GoInterface.ok ri ∧ 0 ≤ sint.Z v.r' ∧ sint.Z v.r' ≤ sint.Z v.w' ∧
      sint.nat v.w' ≤ bs.length ∧ 0 < bs.length ∧ bs.length ≤ 2 ^ 12)
    (Herr : v.err' ≠ GoInterface.nil → E (r ++ subslice (sint.nat v.r') (sint.nat v.w') bs) v.err') :
    isPkgInit (PROP := IProp GF) pkg_id.bufio -∗ b ↦ v -∗ v.buf' ↦* bs -∗
      S (r ++ subslice (sint.nat v.r') (sint.nat v.w') bs) -∗ bufio.ownReader b ri S E r := by
  iintro #Hpkg Hv Hbuf HS
  iunfold bufio.ownReader
  isplitr
  · iexact Hpkg
  iexists v, bs
  iframe Hv Hbuf HS
  ipureintro
  exact ⟨Hwf, Herr⟩

set_option hygiene false in
/-- The copy at the end of `Read` (`n = copy(p, b.buf[b.r:b.w])`, ...) from the reader's
state `V` (`b ↦ V`) and buffer `BS`, with `b.r ≠ b.w` (`Hrw`). -/
local macro "copy_tail " V:term:max BS:term:max : tactic => `(tactic| (
  ihave %Hbwf := ownSlice_wf ($V).buf' _ ($BS) $$ Hbuf
  have hlt : sint.Z ($V).r' < sint.Z ($V).w' := by
    rcases Hwf with ⟨_, h1, h2, _⟩
    have : sint.Z ($V).r' ≠ sint.Z ($V).w' := fun h => Hif (by word)
    omega
  have hwlen : sint.Z ($V).w' ≤ sint.Z ($V).buf'.len := by
    rcases Hwf with ⟨_, _, _, h3, _⟩; rw [Hblen.1] at h3; word
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z ($V).r' ∧ sint.Z ($V).r' ≤ sint.Z ($V).w' ∧
      sint.Z ($V).w' ≤ sint.Z ($V).buf'.cap from ⟨Hwf.2.1, Hwf.2.2.1, by omega⟩))]
  icases (ownSlice_slice ($V).r' ($V).w' ($V).buf' (DFrac.own 1) ($BS) ⟨Hwf.2.1, Hwf.2.2.1, hwlen⟩).mp $$ Hbuf
    with ⟨Hb0, Hbm, Hb1⟩
  wp_apply (wp_slice_copy p xs _ _ (DFrac.own 1)) $$ [Hp Hbm] as %nc ⟨%Hnc, Hp, Hbm⟩
  · iframe
  ihave Hbuf := (ownSlice_slice ($V).r' ($V).w' ($V).buf' (DFrac.own 1) ($BS) ⟨Hwf.2.1, Hwf.2.2.1, hwlen⟩).mpr $$ [Hb0 Hbm Hb1]
  · iframe
  try wp_auto
  have hsublen : (subslice (sint.nat ($V).r') (sint.nat ($V).w') ($BS)).length =
      sint.nat ($V).w' - sint.nat ($V).r' :=
    bufio.subslice_length _ _ ($BS) Hwf.2.2.2.1
  have hxpos : 0 < xs.length := by rw [Hplen.1]; revert hp0; word
  have hnc1 : 1 ≤ sint.nat nc ∧ sint.nat nc ≤ sint.nat ($V).w' - sint.nat ($V).r' := by
    rw [Hnc, hsublen]; constructor <;> word
  have hrnc : sint.Z (($V).r' + nc) = sint.Z ($V).r' + sint.Z nc := by word
  have hidx : sint.Z (($V).r' + nc - W64 1) = sint.Z ($V).r' + sint.Z nc - 1 := by word
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show _ ∧ _ from ⟨by word, by word⟩))]
  obtain ⟨x, hx⟩ : ∃ x, ($BS)[(sint.Z (($V).r' + nc - W64 1)).toNat]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by word)⟩
  wp_apply (wp_load_slice_index ($V).buf' _ ($BS) (DFrac.own 1) x (by word)) $$ [Hbuf] as Hbuf
  · iframe; ipureintro; exact hx
  try wp_auto
  have hnat : sint.nat (($V).r' + nc) = sint.nat ($V).r' + sint.nat nc := by word
  have hl : r ++ subslice (sint.nat ($V).r') (sint.nat ($V).w') ($BS) =
      (r ++ (subslice (sint.nat ($V).r') (sint.nat ($V).w') ($BS)).take (sint.nat nc)) ++
        subslice (sint.nat (($V).r' + nc)) (sint.nat ($V).w') ($BS) := by
    rw [List.append_assoc, hnat, ← bufio.subslice_take_split]
  have hp' := bufio.copy_list xs (subslice (sint.nat ($V).r') (sint.nat ($V).w') ($BS))
  rw [← Hnc] at hp'
  have hyl : ((subslice (sint.nat ($V).r') (sint.nat ($V).w') ($BS)).take (sint.nat nc)).length =
      sint.nat nc := List.length_take_of_le (hsublen ▸ hnc1.2)
  iapply HΦ
  iexists (subslice (sint.nat ($V).r') (sint.nat ($V).w') ($BS)).take (sint.nat nc)
  rw [← hp']
  iframe Hp
  isplitr
  · ipureintro
    refine ⟨by rw [hyl]; word, by rw [hyl, Hnc]; exact Nat.min_le_left _ _, fun h => (h rfl).elim⟩
  rw [hl] at Herr
  iapply (bufio.ownReader_intro b ri S E _
    { ($V) with r' := ($V).r' + nc, lastByte' := W64 (uint.Z x), lastRuneSize' := W64 (-1) } ($BS)
    ⟨Hwf.1, by word, by word, Hwf.2.2.2⟩ Herr) $$ Hpkg Hv Hbuf
  rw [← hl]
  iexact HS))

set_option maxHeartbeats 800000 in
theorem bufio.Reader.Read.wp_proof : bufio.Reader.Read.spec (GF := GF) (hG := hG) := by
  intro b ri S E r p xs
  iintro #Hrd #HSb
  wp_start as ⟨%Hrx, Hb, Hp⟩
  iunfold bufio.ownReader at Hb
  icases Hb with ⟨#Hpkg, %v, %bs, Hv, Hbuf, %Hwf, HS, %Herr⟩
  ihave %Hplen := ownSlice_len _ _ _ $$ Hp
  ihave %Hblen := ownSlice_len _ _ _ $$ Hbuf
  try wp_auto
  wp_if_destruct
  · wp_apply (bufio.wp_Buffered b v) $$ Hv as Hv
    try wp_auto
    wp_if_destruct
    · try wp_auto
      iapply HΦ
      iexists []
      simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
      iframe Hp
      isplitr
      · ipureintro; exact ⟨by word, Nat.zero_le _, fun h => absurd rfl h⟩
      iapply (bufio.ownReader_intro b ri S E r v bs Hwf Herr) $$ Hpkg Hv Hbuf HS
    · wp_apply (bufio.wp_readErr b v) $$ Hv as Hv
      try wp_auto
      have hrw : v.r' = v.w' := by rcases Hwf with ⟨_, h1, h2, _⟩; revert Hif h1 h2; word
      have hsub : subslice (sint.nat v.r') (sint.nat v.w') bs = [] := by
        rw [hrw]; simp [subslice]
      rw [hsub, List.append_nil] at Herr
      iapply HΦ
      iexists []
      simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
      iframe Hp
      isplitr
      · ipureintro; exact ⟨by word, Nat.zero_le _, Herr⟩
      iapply (bufio.ownReader_intro b ri S E r { v with err' := GoInterface.nil } bs Hwf (fun h => (h rfl).elim)) $$ Hpkg Hv Hbuf
      simp only [hsub, List.append_nil]
      iexact HS
  · have hp0 : p.len ≠ W64 0 := Hif
    try wp_auto
    wp_if_destruct
    · have hsub : subslice (sint.nat v.r') (sint.nat v.w') bs = [] := by
        rw [Hif]; simp [subslice]
      rw [hsub, List.append_nil] at Herr
      rcases hve : v.err' with e | _
      · rw [hve] at Herr
        simp only []
        try wp_auto
        wp_apply (bufio.wp_readErr b v) $$ Hv as Hv
        try wp_auto
        iapply HΦ
        iexists []
        simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
        iframe Hp
        isplitr
        · ipureintro; exact ⟨by word, Nat.zero_le _, by rw [hve]; exact Herr⟩
        iapply (bufio.ownReader_intro b ri S E r { v with err' := GoInterface.nil } bs Hwf
          (fun h => (h rfl).elim)) $$ Hpkg Hv Hbuf
        simp only [hsub, List.append_nil]
        iexact HS
      · simp only []
        try wp_auto
        wp_if_destruct
        · try wp_auto
          rw [Hwf.1, hsub, List.append_nil]
          try wp_auto
          iunfold io.readerStream at Hrd
          wp_apply Hrd $$ %r %p %xs [HS Hp] as %nr %er ⟨%ys, %Hys, Hp, HS⟩
          · iframe; ipureintro; exact Hrx
          have hnr0 : ¬ sint.Z nr < 0 := by omega
          wp_if_destruct
          · exact absurd Hif hnr0
          have hyl : ys.length ≤ sint.nat p.len := by omega
          wp_if_destruct
          · obtain ⟨x, hx⟩ : ∃ x, (ys ++ xs.drop ys.length)[(sint.Z (nr - W64 1)).toNat]? = some x :=
              ⟨_, List.getElem?_eq_getElem (by rw [List.length_append]; word)⟩
            try wp_auto
            rw [ite_eq_left_of_eq_true _ _ (eq_true (show _ ∧ _ from ⟨by word, by word⟩))]
            wp_apply (wp_load_slice_index p _ _ (DFrac.own 1) x (by word)) $$ [Hp] as Hp
            · iframe; ipureintro; exact hx
            try wp_auto
            wp_apply (bufio.wp_readErr b _) $$ Hv as Hv
            try wp_auto
            iapply HΦ
            iexists ys
            iframe Hp
            isplitr
            · ipureintro; exact Hys
            iapply (bufio.ownReader_intro b ri S E _
              { v with err' := GoInterface.nil, lastByte' := W64 (uint.Z x), lastRuneSize' := W64 (-1) }
              bs Hwf (fun h => (h rfl).elim)) $$ Hpkg Hv Hbuf
            simp only [hsub, List.append_nil]
            iexact HS
          · try wp_auto
            wp_apply (bufio.wp_readErr b _) $$ Hv as Hv
            try wp_auto
            iapply HΦ
            iexists ys
            iframe Hp
            isplitr
            · ipureintro; exact Hys
            iapply (bufio.ownReader_intro b ri S E _ { v with err' := GoInterface.nil }
              bs Hwf (fun h => (h rfl).elim)) $$ Hpkg Hv Hbuf
            simp only [hsub, List.append_nil]
            iexact HS
        · try wp_auto
          rw [Hwf.1, hsub, List.append_nil]
          iunfold io.readerStream at Hrd
          ihave %HSr := HSb $$ HS
          wp_apply Hrd $$ %r %v.buf' %bs [HS Hbuf] as %nr %er ⟨%ys, %Hys, Hbuf, HS⟩
          · iframe; ipureintro; have := Hwf.2.2.2.2.2; omega
          have hnr0 : ¬ sint.Z nr < 0 := by omega
          wp_if_destruct
          · exact absurd Hif hnr0
          have hys0 : ys.length ≤ bs.length := Hys.2.1
          wp_if_destruct
          · have hys : ys = [] := List.eq_nil_of_length_eq_zero (by
              have h0 : ((ys.length : Nat) : Int) = 0 := Hys.1.symm.trans (by decide)
              exact_mod_cast h0)
            subst hys
            try wp_auto
            wp_apply (bufio.wp_readErr b _) $$ Hv as Hv
            try wp_auto
            iapply HΦ
            iexists []
            simp only [List.append_nil, List.length_nil, List.drop_zero, List.nil_append]
            simp only [List.append_nil, List.length_nil] at Hys
            iframe Hp
            isplitr
            · ipureintro; exact ⟨by word, Nat.zero_le _, Hys.2.2⟩
            iapply (bufio.ownReader_intro b ri S E r (_root_.Perennial.bufio.Reader.mk v.buf'
              (GoInterface.ok ri) (W64 0) (W64 0) GoInterface.nil v.lastByte' v.lastRuneSize') bs
              ⟨rfl, by word, by word, by word, Hwf.2.2.2.2⟩ (fun h => (h rfl).elim)) $$ Hpkg Hv Hbuf
            have h00 : subslice (sint.nat (W64 0)) (sint.nat (W64 0)) bs = [] := by simp [subslice]
            simp only [h00, List.append_nil]
            iexact HS
          · try wp_auto
            have hBS : (ys ++ bs.drop ys.length).length = bs.length :=
              bufio.length_append_drop ys bs hys0
            have hw : sint.nat (W64 0 + nr) = ys.length := by word
            have hsub2 : subslice (sint.nat (W64 0)) (sint.nat (W64 0 + nr)) (ys ++ bs.drop ys.length) = ys := by
              rw [hw]; exact bufio.subslice_prefix ys _
            have Hwf0 : 0 < bs.length ∧ bs.length ≤ 2 ^ 12 := Hwf.2.2.2.2
            have Hblen0 := Hblen
            have hnr : nr ≠ W64 0 := Hif
            clear Hwf Hblen Herr Hif
            let V : _root_.Perennial.bufio.Reader := _root_.Perennial.bufio.Reader.mk v.buf'
              (GoInterface.ok ri) (W64 0) (W64 0 + nr) er v.lastByte' v.lastRuneSize'
            have hV : V = _root_.Perennial.bufio.Reader.mk v.buf'
              (GoInterface.ok ri) (W64 0) (W64 0 + nr) er v.lastByte' v.lastRuneSize' := rfl
            let BS := ys ++ bs.drop ys.length
            have Hwf : V.rd' = GoInterface.ok ri ∧ 0 ≤ sint.Z V.r' ∧ sint.Z V.r' ≤ sint.Z V.w' ∧
                sint.nat V.w' ≤ BS.length ∧ 0 < BS.length ∧ BS.length ≤ 2 ^ 12 := by
              refine ⟨rfl, by simp only [hV]; word, by simp only [hV]; word, ?_, ?_⟩ <;> rw [hBS]
              · simp only [hV]; rw [hw]; exact hys0
              · exact Hwf0
            have Hblen : BS.length = sint.nat V.buf'.len ∧ 0 ≤ sint.Z V.buf'.len := by
              rw [hBS]; exact Hblen0
            have hsubV : subslice (sint.nat V.r') (sint.nat V.w') BS = ys := hsub2
            have Herr : V.err' ≠ GoInterface.nil →
                E (r ++ subslice (sint.nat V.r') (sint.nat V.w') BS) V.err' := by
              rw [hsubV]; exact Hys.2.2
            have Hif : ¬ V.r' = V.w' := by simp only [hV]; revert hnr; word
            rw [show r ++ ys = r ++ subslice (sint.nat V.r') (sint.nat V.w') BS by rw [hsubV]]
            copy_tail V BS
    · copy_tail v bs

end proof

end EtcdGrove
end Perennial

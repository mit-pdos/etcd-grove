/-
The proof of `Decoder.fetch_conn.spec` (`Spec/encoding/json/Codec/Decoder__fetch_conn.lean`): the
buffer's first allocation (64 bytes), the move of the kept bytes to the front (grown: `make` and
`append`; in place: `copy(buf[:cap], buf[prevStart:])`, a copy within one array,
`wp_slice_copy_within_int`), then the read into the free space over `net.Conn.Read.specLc` (the
protocol's fact, under a later in `recvTokL`, stripped with the read's credit), at an end that reads
nothing more (`read_after_dead_au`) or not (`read_au_dead`). The free space is never empty, so a read
returns bytes or an error, and the loop ends after one read. Lean-first (no Rocq counterpart).
-/
module

public import Spec.encoding.json.Codec.Decoder__fetch_conn
public import Net.Spec.net.Conn__Read
public import Proof.net.ErrOrNil
public import Proof.encoding.json.NetInit
public import Proof.net.ReadAuDead
public import Proof.encoding.json.SliceLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace encoding.json

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : encoding.json.Assumptions]
variable [HasExt netExt] [net.Assumptions] [π : NetProtoGS]

/-- The capacity bound after growing (`cap*2`): the capacity was small, or three quarters of it
are kept bytes, fewer than `2^60`. -/
theorem grow_cap_bound (cap len : Int)
    (hg : cap ≤ 2048 ∨ (3 * cap / 4 ≤ len ∧ len < 2 ^ 60)) : 3 * (2 * cap) < 2 ^ 63 := by
  omega

/-- What `copy(buf[:cap], buf[k:len])` leaves in the buffer's first `len - k` bytes (`bs` the
buffer, `vc` its capacity): the kept ones. -/
theorem copy_front_contents (bs vc : List w8) (k len cap n : Nat) (hlen : bs.length = len)
    (hk : k ≤ len) (hcap : len ≤ cap) (hn : n = len - k) :
    subslice (sint.nat (W64 0)) n (List.take 0 (bs ++ vc) ++
      (List.take (cap - 0) (subslice k len (bs ++ vc)) ++
        List.drop (len - k) (subslice 0 cap (bs ++ vc))) ++ List.drop cap (bs ++ vc)) =
      bs.drop k := by
  have hs : subslice k len (bs ++ vc) = bs.drop k := by
    simp only [subslice]
    rw [List.take_append_of_le_length (by omega), ← hlen, List.take_length]
  have h0 : sint.nat (W64 0) = 0 := rfl
  rw [hs, h0, List.take_zero, List.nil_append, Nat.sub_zero,
    List.take_of_length_le (by simp; omega)]
  simp only [subslice, List.drop_zero, List.append_assoc]
  rw [List.take_append_of_le_length (by simp; omega), List.take_of_length_le (by simp; omega)]

theorem Decoder.fetch_conn.wp_proof (wp_Read : net.Conn.Read.specLc (GF := GF) (hG := hG)) :
    Decoder.fetch_conn.spec (GF := GF) (hG := hG) := by
  intro dec d bs cn s a P R dead ue Hok Hkept
  wp_start as ⟨#Hue, #Hc, Hd, Hb, Hcap, Htok, Hdead⟩
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  wp_auto
  -- the first allocation: a buffer with room
  wp_join iprop(∃ b1 : GoSlice, dec_ptr ↦ dec ∗ dec ↦ { d with buf' := b1 } ∗ b1 ↦* bs ∗
      ownSliceCap w8 b1 (DFrac.own 1) ∗ ⌜0 < sint.Z b1.cap ∧ 3 * sint.Z b1.cap < 2 ^ 63⌝)
    with [dec Hd Hb Hcap] as ⟨%b1, dec, Hd, Hb, Hcap, %Hb1⟩
  · wp_apply wp_slice_make3 (V := w8) (W64 0) (W64 64) ⟨by decide, by decide⟩
      as %nb ⟨Hnb, Hncap, %Hnc⟩
    have hbs : bs = [] := by
      rw [Hif] at Hcw; apply List.eq_nil_of_length_eq_zero; word
    subst hbs
    isplitl []
    · ipureintro; rfl
    iexists nb
    iframe Hncap dec
    isplitl [Hd]
    · iexact Hd
    isplitl [Hnb]
    · simp only [List.replicate_zero]; iexact Hnb
    ipureintro; rw [Hnc]; decide
  · iexists d.buf'
    iframe
    ipureintro; constructor
    · rcases Hcw with ⟨h1, h2⟩
      have : sint.Z d.buf'.cap ≠ 0 := fun h => Hif (by word)
      omega
    · exact Hok.2.2.2
  ihave %Hbl1 := ownSlice_len _ _ _ $$ Hb
  ihave %Hcw1 := ownSliceCap_wf _ _ $$ Hcap
  -- the decision to grow
  wp_join (Q := fun v => iprop(∃ g1 : Bool, ⌜v = #g1 ∧
      (g1 = true → sint.Z b1.cap ≤ 2048)⌝ ∗ dec_ptr ↦ dec ∗ dec ↦ { d with buf' := b1 }))
    at (If _ _ _) with [dec Hd]
  · wp_if_destruct
    · iexists _
      iframe
      ipureintro
      exact ⟨rfl, fun _ => by word⟩
    · iexists false
      iframe
      ipureintro
      exact ⟨rfl, fun h => by cases h⟩
  rename_i v
  iintro ⟨%g1, ⟨%Hv, %Hg1⟩, dec, Hd⟩
  subst Hv
  wp_auto
  wp_join (Q := fun v => iprop(∃ g : Bool, ⌜v = #g ∧
      (g = true → sint.Z b1.cap ≤ 2048 ∨
        (d.prevStart' = W64 0 ∧ 3 * sint.Z b1.cap / 4 ≤ sint.Z b1.len)) ∧
      (g = false → ¬ (d.prevStart' = W64 0 ∧ 3 * sint.Z b1.cap / 4 ≤ sint.Z b1.len))⌝ ∗
      dec_ptr ↦ dec ∗ dec ↦ { d with buf' := b1 }))
    at (If _ _ _) with [dec Hd]
  · wp_if_destruct
    · wp_if_destruct
      · iexists _
        iframe
        ipureintro
        have hdiv : sint.Z (BitVec.sdiv (W64 3 * b1.cap) (W64 4)) = 3 * sint.Z b1.cap / 4 := by
          word
        rw [hdiv]
        refine ⟨rfl, fun h => Or.inr ⟨Hif, of_decide_eq_true h⟩,
          fun h hh => absurd hh.2 (of_decide_eq_false h)⟩
      · iexists false
        iframe
        ipureintro
        exact ⟨rfl, fun h => (by cases h), fun _ h => (by simp_all)⟩
    · iexists true
      iframe
      ipureintro
      exact ⟨rfl, fun _ => Or.inl (Hg1 (by simp_all)), fun h => (by cases h)⟩
  rename_i v
  iintro ⟨%g, ⟨%Hv, %Hg⟩, dec, Hd⟩
  subst Hv
  wp_auto
  have hps : sint.Z d.prevStart' ≤ sint.Z b1.len := by
    have h1 := Hok.2.2.1; have h2 := Hok.2.1; have h3 := Hbl1.1; have h4 := Hbl1.2
    have h5 : (bs.length : Int) = sint.Z b1.len := by rw [h3]; word
    omega
  -- the kept bytes to the front
  wp_join iprop(∃ b2 : GoSlice, dec_ptr ↦ dec ∗ dec ↦ { d with buf' := b2 } ∗
      b2 ↦* bs.drop (sint.nat d.prevStart') ∗ ownSliceCap w8 b2 (DFrac.own 1) ∗
      ⌜3 * sint.Z b2.cap < 2 ^ 63 ∧ sint.Z b2.len < sint.Z b2.cap⌝)
    with [dec Hd Hb Hcap] as ⟨%b2, dec, Hd, Hb, Hcap, %Hb2⟩
  · -- in place: `copy(buf[:cap], buf[prevStart:])`, within the array
    have h00 : sint.Z (W64 0) = 0 := rfl
    have hps0 : 0 ≤ sint.Z d.prevStart' := Hok.1
    have hps63 : sint.Z d.prevStart' < 2 ^ 63 := by word
    have h0le : 0 ≤ sint.Z (W64 0) := Int.le_of_eq h00.symm
    have h0cap : sint.Z (W64 0) ≤ sint.Z b1.cap := by rw [h00]; exact Int.le_trans Hcw1.1 Hcw1.2
    rw [ite_eq_left ⟨h0le, h0cap, Int.le_refl _⟩]
    wp_auto
    rw [ite_eq_left ⟨hps0, hps, Hcw1.2⟩]
    wp_auto
    icases ownSlice_slice_into_capacity (W64 0) b1.cap b1 bs $$ [Hb Hcap] with
      ⟨%vc, -, Hfull, Hfcap⟩
    · iframe; ipureintro; exact ⟨h0le, h0cap, Hcw1.2, Int.le_refl _⟩
    simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    ihave %Hfl := ownSlice_len _ _ _ $$ Hfull
    have hfl : (slice.slice b1 w8 (W64 0) b1.cap).len = b1.cap := by simp [slice.slice]
    have hov : 0 ≤ sint.Z (W64 0) + sint.Z d.prevStart' ∧
        sint.Z (W64 0) + sint.Z d.prevStart' < 2 ^ 63 := by rw [h00]; omega
    have hsrc : slice.slice b1 w8 d.prevStart' b1.len =
        slice.slice (slice.slice b1 w8 (W64 0) b1.cap) w8 d.prevStart' b1.len := by
      rw [slice_slice b1 (W64 0) b1.cap d.prevStart' b1.len hov]
      congr 1 <;> word
    have hdst : slice.slice b1 w8 (W64 0) b1.cap =
        slice.slice (slice.slice b1 w8 (W64 0) b1.cap) w8 (W64 0)
          (slice.slice b1 w8 (W64 0) b1.cap).len := slice_slice_trivial _
    rw [hsrc]
    conv in (Val #(slice.slice b1 w8 (W64 0) b1.cap)) => rw [hdst]
    have hcapc : sint.Z (W64 0) ≤ sint.Z (slice.slice b1 w8 (W64 0) b1.cap).len := by
      rw [hfl]; exact h0cap
    have hcapc2 : sint.Z (slice.slice b1 w8 (W64 0) b1.cap).len ≤
        sint.Z (slice.slice b1 w8 (W64 0) b1.cap).len := Int.le_refl _
    have hlenc : sint.Z b1.len ≤ sint.Z (slice.slice b1 w8 (W64 0) b1.cap).len := by
      rw [hfl]; exact Hcw1.2
    wp_apply wp_slice_copy_within_int (slice.slice b1 w8 (W64 0) b1.cap) (bs ++ vc) (W64 0)
      (slice.slice b1 w8 (W64 0) b1.cap).len d.prevStart' b1.len
      ⟨h0le, hcapc, hcapc2⟩
      ⟨hps0, hps, hlenc⟩ $$ Hfull as %n ⟨%Hn, Hfull⟩
    have hbl : bs.length = sint.nat b1.len := Hbl1.1
    have hnZ : sint.Z n = sint.Z b1.len - sint.Z d.prevStart' := by
      rw [Hn, hfl]; simp only [show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero]
      have : sint.nat b1.len - sint.nat d.prevStart' ≤ sint.nat b1.cap := by word
      rw [Int.min_eq_right (by omega)]; word
    have hn0 : 0 ≤ sint.Z n := by omega
    have hncap : sint.Z n ≤ sint.Z b1.cap := by omega
    rw [ite_eq_left ⟨h0le, by rw [h00]; exact hn0, hncap⟩]
    wp_auto
    isplitl []
    · ipureintro; rfl
    ihave %Hfcw := ownSliceCap_wf _ _ $$ Hfcap
    icases ownSlice_slice_with_cap (W64 0) n (slice.slice b1 w8 (W64 0) b1.cap) _
      ⟨h0le, by rw [h00]; exact hn0, by rw [hfl]; exact hncap⟩ $$ [Hfull Hfcap]
      with ⟨-, Hnew, Hncap⟩
    · iframe
    have hss : slice.slice (slice.slice b1 w8 (W64 0) b1.cap) w8 (W64 0) n =
        slice.slice b1 w8 (W64 0) n := by
      rw [slice_slice b1 (W64 0) b1.cap (W64 0) n (by rw [h00]; decide)]
      congr 1; word
    rw [hss]
    iexists (slice.slice b1 w8 (W64 0) n)
    iframe dec Hd Hncap
    isplitl [Hnew]
    · rw [copy_front_contents bs vc (sint.nat d.prevStart') (sint.nat b1.len)
        (sint.nat (b1.cap - W64 0)) (sint.nat n) hbl (by word) (by word) (by word)]
      iexact Hnew
    ipureintro
    simp only [slice.slice]
    constructor
    · have : sint.Z (b1.cap - W64 0) = sint.Z b1.cap := by word
      rw [this]; exact Hb1.2
    · have : sint.Z (n - W64 0) = sint.Z n := by word
      have h2 : sint.Z (b1.cap - W64 0) = sint.Z b1.cap := by word
      rw [this, h2]
      by_cases h : d.prevStart' = W64 0
      · have hlt := Hg.2 rfl
        have : ¬ (3 * sint.Z b1.cap / 4 ≤ sint.Z b1.len) := fun h' => hlt ⟨h, h'⟩
        have : sint.Z d.prevStart' = 0 := by rw [h]; rfl
        omega
      · have : sint.Z d.prevStart' ≠ 0 := fun h' => h (by word)
        omega
  · -- grown: a new array of twice the capacity, the kept bytes appended to it
    have hcap2 : sint.Z (b1.cap * W64 2) = 2 * sint.Z b1.cap := by word
    wp_apply wp_slice_make3 (V := w8) (W64 0) (b1.cap * W64 2) ⟨by decide, by rw [hcap2, show sint.Z (W64 0) = 0 from rfl]; omega⟩
      as %nb ⟨Hnb, Hncap, %Hnc⟩
    ihave %Hnbl := ownSlice_len _ _ _ $$ Hnb
    have hnb0 : nb.len = W64 0 := by simp at Hnbl; word
    icases (ownSlice_split_all d.prevStart' b1 _ bs ⟨Hok.1, hps⟩).1 $$ Hb with ⟨-, Hsrc⟩
    ihave %Hsrcl := ownSlice_len _ _ _ $$ Hsrc
    have hsrcl : (slice.slice b1 w8 d.prevStart' b1.len).len = b1.len - d.prevStart' := rfl
    have hk : sint.Z (b1.len - d.prevStart') = sint.Z b1.len - sint.Z d.prevStart' := by
      have := Hok.1; word
    have h00 : sint.Z (W64 0) = 0 := rfl
    have hz0 : W64 0 + (b1.len - d.prevStart') = b1.len - d.prevStart' := by word
    have hfit : sint.Z (b1.len - d.prevStart') ≤ 2 * sint.Z b1.cap := by
      rw [hk]; have := Hok.1; omega
    rw [ite_eq_left ⟨Hok.1, hps, Hcw1.2⟩]
    wp_auto
    wp_bind (App (App (Val #(functions go.append [go.byte.SliceType])) (Val #nb))
      (Val #(slice.slice b1 w8 d.prevStart' b1.len)))
    iapply wp_slice_append_fits nb (slice.slice b1 w8 d.prevStart' b1.len) _
      ⟨by rw [hnb0]; decide, by rw [hsrcl, hk]; omega⟩
      (by rw [hnb0, hsrcl, Hnc, hcap2, h00]; omega)
    icases ownSliceCap_split (nb.len + (slice.slice b1 w8 d.prevStart' b1.len).len) nb $$ [Hncap]
      with ⟨%vs', Hdst, Hdcap⟩
    · iframe; ipureintro; rw [hnb0, hsrcl, Hnc, hcap2, h00, hz0]; constructor <;> omega
    ihave %Hdl := ownSlice_len _ _ _ $$ Hdst
    wp_apply wp_slice_copy $$ [Hdst Hsrc] as %n ⟨%Hn, Hdst, -⟩
    · iframe
    isplitl []
    · ipureintro; exact isPanic_intoVal _
    imodintro
    wp_auto
    isplitl []
    · ipureintro; rfl
    have hlenk : vs'.length = (List.drop (sint.nat d.prevStart') bs).length := by
      rw [Hdl.1, Hsrcl.1]; simp [slice.slice, hnb0]
    have hdn : List.drop (List.drop (sint.nat d.prevStart') bs).length vs' = [] :=
      List.drop_of_length_le (Nat.le_of_eq hlenk)
    simp only [hlenk, List.take_length, hdn, List.append_nil, hnb0, hsrcl, hz0]
    iexists (slice.slice nb w8 (W64 0) (b1.len - d.prevStart'))
    iframe dec Hd Hdst Hdcap
    ipureintro
    have hlt : sint.Z (b1.len - d.prevStart') < 2 * sint.Z b1.cap := by
      rw [hk]; have := Hok.1; omega
    simp only [slice.slice, Hnc]
    constructor
    · have hc2 : sint.Z (b1.cap * W64 2 - W64 0) = 2 * sint.Z b1.cap := by
        rw [← hcap2]; congr 1; word
      rw [hc2]
      apply grow_cap_bound _ (sint.Z b1.len)
      rcases Hg.1 rfl with h | ⟨h1, h2⟩
      · exact .inl h
      · refine .inr ⟨h2, ?_⟩
        have hk0 : sint.nat d.prevStart' = 0 := by rw [h1]; rfl
        have hbl : bs.length < 2 ^ 60 := by have := Hkept; rw [hk0] at this; omega
        have hb : (bs.length : Int) = sint.Z b1.len := by rw [Hbl1.1]; word
        omega
    · word
  -- the reads
  ihave ⟨%ed, #Hed⟩ := ed_of_net $$ Hpkg2
  ihave ⟨%xe, #Heof⟩ := eof_of_net $$ Hpkg2
  ihave #Hc' := Hc
  unfold net.isConn
  icases Hc' with ⟨%t, %la, %ra, %Hct, #Hca⟩
  ihave HI : (dec_ptr ↦ dec ∗
      dec ↦ Decoder.mk d.r' b2 (W64 0) (d.prevEnd' - d.prevStart') (d.baseOffset' + d.prevStart') d.err' d.useNumber' ∗
      b2 ↦* bs.drop (sint.nat d.prevStart') ∗ ownSliceCap w8 b2 (DFrac.own 1) ∗
      recvTok (Gg := hG.goose_globalGS) cn s P R ∗
      (if dead then readDead (Gg := hG.goose_globalGS) cn s else True) ∗
      «$res0_ptr» ↦ GoInterface.nil : IProp GF) $$ [dec Hd Hb Hcap Htok Hdead «$res0»]
  · iframe
  wp_for HI
  icases HI with ⟨dec, Hd, Hb, Hcap, Htok, Hdead, Hres⟩
  ihave %Hbl2 := ownSlice_len _ _ _ $$ Hb
  wp_auto
  have hb2c : 0 ≤ sint.Z b2.len ∧ sint.Z b2.len ≤ sint.Z b2.cap ∧ sint.Z b2.cap ≤ sint.Z b2.cap :=
    ⟨Hbl2.2, Int.le_of_lt Hb2.2, Int.le_refl _⟩
  rw [ite_eq_left hb2c]
  icases ownSliceCap_split (V := w8) b2.cap b2 $$ [Hcap] with ⟨%vs0, Hfree, Hcap⟩
  · iframe Hcap; ipureintro; exact ⟨Int.le_of_lt Hb2.2, Int.le_refl _⟩
  ihave %Hfl := ownSlice_len _ _ _ $$ Hfree
  rw [Hct]
  wp_auto
  iapply wp_fupd
  icases recvTok_proto (Gg := hG.goose_globalGS) cn s _ _ $$ Htok with ⟨Htok, #Hpp0⟩
  ihave HrL := recvTok_L (Gg := hG.goose_globalGS) cn s _ _ $$ Htok
  have hsl : (slice.slice b2 w8 b2.len b2.cap).len = b2.cap - b2.len := rfl
  have hLZ : sint.Z (b2.cap - b2.len) = sint.Z b2.cap - sint.Z b2.len := by
    have := Hbl2.2; have := Hb2.2; word
  have hnn : 0 ≤ sint.Z (b2.cap - b2.len) := by rw [hLZ]; have := Hb2.2; omega
  have hL : (slice.slice b2 w8 b2.len b2.cap).len.toNat = vs0.length := by
    rw [Hfl.1, hsl]; unfold sint.nat; word
  have hLpos : 0 < vs0.length := by
    have hp : 0 < sint.Z (b2.cap - b2.len) := by rw [hLZ]; have := Hb2.2; omega
    rw [Hfl.1, hsl, show sint.nat (b2.cap - b2.len) = (sint.Z (b2.cap - b2.len)).toNat from rfl]
    omega
  cases dead
  · -- reading not known dead
    wp_apply wp_Read t cn s a la ra (slice.slice b2 w8 b2.len b2.cap) vs0
        (interface.mkOk errors.errorString.ty.PointerType #xe) ed
        (fun res => iprop(recvTokL (Gg := hG.goose_globalGS) cn s P (R ++ res.got) ∗
          ⌜∃ st d d', ReadOutcome st d (slice.slice b2 w8 b2.len b2.cap).len.toNat res d'⌝ ∗
          (⌜res = .eof ∨ res = .err .sys ∨ res = .err .closed⌝ -∗
            readDead (Gg := hG.goose_globalGS) cn s))) $$ [Hfree HrL]
      as %k %err ⟨%res, %bs', ⟨HrL, %Hro, Hdead'⟩, Hfree, %Hout, HE, Hlc1, Hlc2⟩
    · iframe Hca Hfree Heof Hed
      iapply read_au_dead (Gg := hG.goose_globalGS) cn s _ _ _ $$ HrL
    obtain ⟨st, dd, dd', Hro⟩ := Hro
    have Hgl := readOutcome_got_le Hro
    rw [hL] at Hro Hgl
    ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn s _ _ $$ HrL
    imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HrT with HrT
    rcases res with got | _ | ek
    · -- bytes: `n > 0`
      simp only [net.ReadErr]
      icases HE with %Herr
      subst Herr
      obtain ⟨hk, hbs'⟩ := Hout
      have hpos := readOutcome_bytes_pos Hro hLpos
      simp only [ReadRes.got] at Hgl
      have hgl : got.length ≤ vs0.length := Hgl.1
      have hkZ : sint.Z k = got.length := by rw [hk]; rw [Nat.min_eq_right hgl]
      wp_if_destruct
      rotate_left
      · exfalso; rw [show sint.Z (W64 0) = 0 from rfl] at Hif; omega
      have hv : (vs0.length : Int) = sint.Z b2.cap - sint.Z b2.len := by
        rw [Hfl.1, hsl, show sint.nat (b2.cap - b2.len) = (sint.Z (b2.cap - b2.len)).toNat from rfl,
          Int.toNat_of_nonneg hnn, hLZ]
      have hglZ : (got.length : Int) ≤ vs0.length := Int.ofNat_le.mpr hgl
      have hbk : sint.Z (b2.len + k) = sint.Z b2.len + got.length := by
        have := Hbl2.2; have := Hb2.2; rw [← hkZ]; word
      have h00 : sint.Z (W64 0) = 0 := rfl
      rw [ite_eq_left ⟨Int.le_refl _, by rw [h00, hbk]; have := Hbl2.2; omega,
        by rw [hbk]; omega⟩]
      wp_auto
      wp_for_post
      imodintro
      wp_auto
      -- the read bytes join the kept ones
      have hkn : sint.nat k = got.length := by
        rw [show sint.nat k = (sint.Z k).toNat from rfl, hkZ]; simp
      have hsl0 : sint.Z (slice.slice b2 w8 b2.len b2.cap).len = sint.Z b2.cap - sint.Z b2.len := by
        rw [hsl, hLZ]
      icases ownSlice_slice_with_cap (W64 0) k (slice.slice b2 w8 b2.len b2.cap) bs'
        ⟨Int.le_refl _, by rw [h00, hkZ]; omega, by rw [hsl0, hkZ]; omega⟩ $$ [Hfree Hcap]
        with ⟨-, Hnew, Hncap⟩
      · iframe
      have hov : 0 ≤ sint.Z b2.len + sint.Z (W64 0) ∧ sint.Z b2.len + sint.Z (W64 0) < 2 ^ 63 := by
        rw [h00]; have := Hbl2.2; have := Hb2.2; omega
      rw [slice_slice b2 b2.len b2.cap (W64 0) k hov, show b2.len + W64 0 = b2.len by word]
        at *
      have hgot : subslice (sint.nat (W64 0)) (sint.nat k) bs' = got := by
        rw [hbs', hkn, show sint.nat (W64 0) = 0 from rfl]
        simp only [subslice, List.drop_zero, List.take_of_length_le hgl]
        rw [List.take_append_of_le_length (by simp), List.take_length]
      rw [hgot]
      ihave Hb := (ownSlice_trivial_slice b2 _ _).1 $$ Hb
      have hbll : (List.drop (sint.nat d.prevStart') bs).length = sint.nat b2.len - sint.nat (W64 0) := by
        rw [Hbl2.1]; rfl
      ihave Hall := ownSlice_combine b2.len b2 (DFrac.own 1) _ got (W64 0) (b2.len + k)
        ⟨hbll, Int.le_refl _, by rw [h00]; exact Hbl2.2, by rw [hbk]; omega⟩ $$ Hb Hnew
      ihave Hncap := ownSliceCap_slice_change_first b2 b2.len (W64 0) (b2.len + k) _
        ⟨by rw [hbk]; omega, Hbl2.2, by rw [hbk]; omega, Int.le_refl _, by rw [h00, hbk]; omega⟩
        $$ Hncap
      iapply HΦ
      iexists (Decoder.mk (interface.mkOk net.TCPConn.ty.PointerType #t)
        (slice.slice b2 w8 (W64 0) (b2.len + k)) (W64 0) (d.prevEnd' - d.prevStart')
        (d.baseOffset' + d.prevStart') d.err' d.useNumber'), got
      simp only [ReadRes.got]
      iframe Hd Hall Hncap HrT
      isplitr
      · ipureintro
        refine ⟨trivial, trivial, rfl, trivial, trivial, ?_⟩
        show 3 * sint.Z (b2.cap - W64 0) < 2 ^ 63
        rw [show b2.cap - W64 0 = b2.cap by word]; exact Hb2.1
      unfold fetchRes
      ileft
      ipureintro
      exact ⟨rfl, fun h => by subst h; simp at hpos, rfl⟩
    · -- EOF: `io.ErrUnexpectedEOF`, the reading dead
      simp only [net.ReadErr]
      icases HE with %Herr
      subst Herr
      obtain ⟨hk0, rfl⟩ := Hout
      subst hk0
      ihave #Hdd := Hdead' $$ %(by simp)
      wp_if_destruct
      · exfalso; exact Int.lt_irrefl _ Hif
      wp_for_post
      imodintro
      wp_auto
      ihave Hcap := ownSliceCap_restore b2 _ ⟨Hbl2.2, Int.le_of_lt Hb2.2⟩ $$ [Hfree Hcap]
      · iframe
      iapply HΦ
      iexists (Decoder.mk (interface.mkOk net.TCPConn.ty.PointerType #t) b2 (W64 0)
        (d.prevEnd' - d.prevStart') (d.baseOffset' + d.prevStart') d.err' d.useNumber'), []
      simp only [ReadRes.got, List.append_nil]
      iframe Hd Hb Hcap HrT
      isplitr
      · ipureintro; exact ⟨trivial, trivial, rfl, trivial, trivial, Hb2.1⟩
      unfold fetchRes
      iright; ileft
      iframe Hdd
      ipureintro; exact ⟨rfl, rfl⟩
    · -- a failure: its `*OpError`
      obtain ⟨hk0, rfl⟩ := Hout
      subst hk0
      simp only [net.ReadErr]
      ihave #Hsys := net.connAt_errnoOk _ _ _ _ _ _ $$ Hca
      ihave #Heo := net.resErr_errOrNil _ _ _ _ _ _ _ $$ Hsys HE
      unfold net.resErr net.opErr
      icases HE with ⟨%e, ⟨%pe, %nw, ⟨%Hpe, %Htcp⟩, -⟩, -⟩
      subst Hpe
      wp_if_destruct
      · exfalso; exact Int.lt_irrefl _ Hif
      wp_for_post
      imodintro
      wp_auto
      ihave Hcap := ownSliceCap_restore b2 _ ⟨Hbl2.2, Int.le_of_lt Hb2.2⟩ $$ [Hfree Hcap]
      · iframe
      iapply HΦ
      iexists (Decoder.mk (interface.mkOk net.TCPConn.ty.PointerType #t) b2 (W64 0)
        (d.prevEnd' - d.prevStart') (d.baseOffset' + d.prevStart') d.err' d.useNumber'), []
      simp only [ReadRes.got, List.append_nil]
      iframe Hd Hb Hcap HrT
      isplitr
      · ipureintro; exact ⟨trivial, trivial, rfl, trivial, trivial, Hb2.1⟩
      unfold fetchRes
      iright; iright
      iframe Heo
      ipureintro; exact ⟨rfl, pe, rfl⟩
  · -- reading dead: no byte
    simp only [ite_true]
    ihave #Hdd := Hdead
    wp_apply wp_Read t cn s a la ra (slice.slice b2 w8 b2.len b2.cap) vs0
        (interface.mkOk errors.errorString.ty.PointerType #xe) ed
        (fun res => iprop(recvTokL (Gg := hG.goose_globalGS) cn s P R ∗
          ⌜res.got = [] ∧ ((slice.slice b2 w8 b2.len b2.cap).len.toNat ≠ 0 →
            ∀ bs, res ≠ .bytes bs)⌝)) $$ [Hfree HrL]
      as %k %err ⟨%res, %bs', ⟨HrL, %Hres⟩, Hfree, %Hout, HE, Hlc1, Hlc2⟩
    · iframe Hca Hfree Heof Hed
      iapply read_after_dead_au (Gg := hG.goose_globalGS) cn s _ _ _ $$ [$HrL $Hdd]
    rw [hL] at Hres
    ihave HrT := recvTokL_later (Gg := hG.goose_globalGS) cn s _ _ $$ HrL
    imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HrT with HrT
    rcases res with got | _ | ek
    · exfalso; exact Hres.2 (by omega) got rfl
    · -- EOF: `io.ErrUnexpectedEOF`
      simp only [net.ReadErr]
      icases HE with %Herr
      subst Herr
      obtain ⟨hk0, rfl⟩ := Hout
      subst hk0
      wp_if_destruct
      · exfalso; exact Int.lt_irrefl _ Hif
      wp_for_post
      imodintro
      wp_auto
      ihave Hcap := ownSliceCap_restore b2 _ ⟨Hbl2.2, Int.le_of_lt Hb2.2⟩ $$ [Hfree Hcap]
      · iframe
      iapply HΦ
      iexists (Decoder.mk (interface.mkOk net.TCPConn.ty.PointerType #t) b2 (W64 0)
        (d.prevEnd' - d.prevStart') (d.baseOffset' + d.prevStart') d.err' d.useNumber'), []
      simp only [List.append_nil]
      iframe Hd Hb Hcap HrT
      isplitr
      · ipureintro; exact ⟨trivial, trivial, rfl, trivial, trivial, Hb2.1⟩
      unfold fetchRes
      iright; ileft
      iframe Hdd
      ipureintro; exact ⟨rfl, rfl⟩
    · -- a failure: its `*OpError`
      obtain ⟨hk0, rfl⟩ := Hout
      subst hk0
      simp only [net.ReadErr]
      ihave #Hsys := net.connAt_errnoOk _ _ _ _ _ _ $$ Hca
      ihave #Heo := net.resErr_errOrNil _ _ _ _ _ _ _ $$ Hsys HE
      unfold net.resErr net.opErr
      icases HE with ⟨%e, ⟨%pe, %nw, ⟨%Hpe, %Htcp⟩, -⟩, -⟩
      subst Hpe
      wp_if_destruct
      · exfalso; exact Int.lt_irrefl _ Hif
      wp_for_post
      imodintro
      wp_auto
      ihave Hcap := ownSliceCap_restore b2 _ ⟨Hbl2.2, Int.le_of_lt Hb2.2⟩ $$ [Hfree Hcap]
      · iframe
      iapply HΦ
      iexists (Decoder.mk (interface.mkOk net.TCPConn.ty.PointerType #t) b2 (W64 0)
        (d.prevEnd' - d.prevStart') (d.baseOffset' + d.prevStart') d.err' d.useNumber'), []
      simp only [List.append_nil]
      iframe Hd Hb Hcap HrT
      isplitr
      · ipureintro; exact ⟨trivial, trivial, rfl, trivial, trivial, Hb2.1⟩
      unfold fetchRes
      iright; iright
      iframe Heo
      ipureintro; exact ⟨rfl, pe, rfl⟩

end proof

end encoding.json
end Perennial

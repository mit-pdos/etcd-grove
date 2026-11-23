/-
Ported from dsverify-lab examples/epaxos/proof/Epaxos/Proof/wire/Varint/ReadUvarint.lean
(notes/dsv-epaxos.md): over dsv-bufio's `Reader.ReadByte.spec` (its error `ptrTyped`, which the
lab's `wp_ReadByte_wf` added), the stream fact a step later (`nextIs_read`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.RProg
public import Proof.bufio.Reader__ReadByte
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Varint.Decode

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem w64_of_w8_toNat (c : w8) : (W64 (uint.Z c)).toNat = c.toNat := by
  have := c.isLt; simp [W64, uint.Z]; omega

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [bufio.Assumptions] [io.Assumptions]

set_option goose.wp.extras true

theorem epaxos.readUvarint.spec_holds (br : Loc) (rd : BufRd GF) (R : List w8) :
  {{ pkgInit_epaxos ∗ isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ rdOwn br rd R ∗ nextIs rd R uvarintEnc (fun n => n < 2 ^ 64) }}
    (App (Val (@! epaxos.readUvarint)) (Val #(brIface br)))
  {{ (u : w64) (err : GoInterface), RET (PairV #u #err);
      (⌜err = interface.nil⌝ ∗ rdOwn br rd (R ++ uvarintEnc u.toNat)) ∨
      (⌜err ≠ interface.nil⌝ ∗ ∃ data : List w8, rdOwn br rd (R ++ data)) }} := by
  wp_start as ⟨Hown, #Hnext⟩
  ihave #Hio := EtcdGrove.bufio.io_init_of_bufio $$ Hpkg2
  ihave #Hioi := io.isInit_access $$ Hio
  icases Hioi with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
  iunfold errors.newVar at HEOF HUEOF
  icases HEOF with ⟨%eofx, #HEOF, -⟩
  icases HUEOF with ⟨%uex, #Hueo, -⟩
  wp_auto
  ihave HL : (∃ (d : List w8) (xv : w64),
      "x" ∷ x_ptr ↦ xv ∗ "s" ∷ s_ptr ↦ W64 (7 * d.length : Nat) ∗
      "i" ∷ i_ptr ↦ W64 (d.length : Nat) ∗ "Hown" ∷ rdOwn br rd (R ++ d) ∗
      "%Hd" ∷ ⌜(∀ c ∈ d, 128 ≤ c.toNat) ∧ xv.toNat = low7 d ∧ d.length ≤ 9⌝ : IProp GF)
    $$ [x s i Hown]
  · iexists [], _
    simp only [List.append_nil, List.length_nil, Nat.mul_zero]
    iframe x i Hown
    rw [show W64 ((0 : Nat) : Int) = zero_val w64 from rfl]
    iframe s
    ipureintro
    exact ⟨by simp, rfl, by decide⟩
  wp_for HL
  obtain ⟨hdc, hxv, hd9⟩ := Hd
  have hdZ : sint.Z (W64 (d.length : Int)) = d.length := sint_Z_W64_length (by omega)
  have hlt : sint.Z (W64 (d.length : Int)) < sint.Z (W64 10) := by
    rw [hdZ]; have : sint.Z (W64 10) = 10 := rfl; omega
  simp only [hlt, _root_.decide_true, ↓reduceIte]
  wp_auto
  wp_apply EtcdGrove.bufio.Reader.ReadByte.wp_proof br rd.ri rd.Pre rd.S rd.E (R ++ d) $$ [$Hown]
    as %c %err Hres
  icases Hres with (⟨%Hen, Hown⟩ | ⟨%Hen, -, %Hewf, Hown⟩)
  · -- a byte
    subst Hen
    ihave ⟨Hown, Hpre⟩ := nextIs_read br rd R (d ++ [c]) uvarintEnc _ $$ [$Hnext Hown]
    · rw [List.append_assoc]; iexact Hown
    imod Hpre with %Hpre
    obtain ⟨n, ext, hn, hpre⟩ := Hpre
    have hcZ : uint.Z c = (c.toNat : Int) := rfl
    have h128 : uint.Z (W8 128) = 128 := rfl
    wp_auto
    wp_if_destruct
    · -- the last byte
      have hc : c.toNat < 128 := by omega
      obtain ⟨he, hnv, h9⟩ := final_byte d hdc c hc n ext hn hpre
      have hres : (xv ||| W64 (uint.Z c) <<< W64 ((7 * d.length : Nat) : Int)).toNat = n := by
        have hx : xv.toNat < 2 ^ (7 * d.length) := by rw [hxv, Nat.pow_mul]; exact low7_lt d
        rw [or_shl_toNat xv _ (7 * d.length) (by omega) hx, w64_of_w8_toNat, hxv, hnv,
          Nat.pow_mul]
        · rw [w64_of_w8_toNat, hxv, Nat.pow_mul, ← hnv]; exact hn
      wp_if_destruct
      · have h9' : d.length = 9 := by
          have := congrArg BitVec.toNat Hif
          simp [W64] at this; omega
        have h1 : uint.Z (W8 1) = 1 := rfl
        wp_if_destruct
        · exfalso; have := h9 h9'; omega
        wp_for_post
        iapply HΦ; ileft
        isplitr
        · ipureintro; rfl
        rw [hres, he]; iexact Hown
      wp_for_post
      iapply HΦ; ileft
      isplitr
      · ipureintro; rfl
      rw [hres, he]; iexact Hown
    · -- a continuation byte
      have hc : 128 ≤ c.toNat := by omega
      wp_for_post
      have hall : ∀ c' ∈ d ++ [c], 128 ≤ c'.toNat := by
        intro c' hc'; rcases List.mem_append.mp hc' with h | h
        · exact hdc c' h
        · simp at h; subst h; exact hc
      have hl9 := cont_length _ hall n ext hn hpre
      simp only [List.length_append, List.length_singleton] at hl9
      have hb : (W64 (uint.Z (c &&& W8 127))).toNat = c.toNat % 128 := by
        have : (c &&& W8 127).toNat = c.toNat % 128 := by
          rw [BitVec.toNat_and]; show c.toNat &&& 127 = _
          rw [show (127 : Nat) = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
        rw [w64_of_w8_toNat, this]
      have hx' := or_shl_toNat xv (W64 (uint.Z (c &&& W8 127))) (7 * d.length) (by omega)
        (by rw [hxv, Nat.pow_mul]; exact low7_lt d)
        (by rw [hb, hxv]; have := low7_lt d; rw [Nat.pow_mul] at *
            have : low7 d + c.toNat % 128 * 128 ^ d.length < 128 ^ (d.length + 1) := by
              rw [Nat.pow_succ]; have : c.toNat % 128 < 128 := Nat.mod_lt _ (by decide)
              have := Nat.mul_le_mul_right (128 ^ d.length) (Nat.le_of_lt_succ this)
              omega
            calc _ < 128 ^ (d.length + 1) := this
              _ ≤ 128 ^ 9 := Nat.pow_le_pow_right (by decide) (by omega)
              _ < 2 ^ 64 := by decide)
      iframe
      iexists d ++ [c], _
      iframe Hown x
      have hs : W64 ((7 * d.length : Nat) : Int) + W64 7 = W64 ((7 * (d ++ [c]).length : Nat) : Int) := by
        simp only [List.length_append, List.length_singleton]; push_cast; word
      have hi : W64 ((d.length : Nat) : Int) + W64 1 = W64 (((d ++ [c]).length : Nat) : Int) := by
        simp only [List.length_append, List.length_singleton]; push_cast; word
      rw [hs, hi]
      iframe s i
      ipureintro
      refine ⟨hall, ?_, by simp; omega⟩
      rw [hx', hb, hxv, low7_append, Nat.pow_mul]
  · -- an error
    rcases err with ei | _
    · wp_auto
      wp_if_destruct
      · -- `i > 0`: `err == io.EOF`?
        by_cases hty : ei.ty = go.GoType.PointerType errors.errorString.ty
        · obtain ⟨l, hl⟩ := Hewf ei _ rfl hty
          simp only [hty, ↓reduceIte]
          rw [hl]
          wp_auto
          wp_if_destruct
          · -- `io.EOF`: `io.ErrUnexpectedEOF`
            wp_for_post
            iapply HΦ; iright
            isplitr
            · ipureintro; simp
            iexists d; iexact Hown
          wp_for_post
          iapply HΦ; iright
          isplitr
          · ipureintro; exact Hen
          iexists d; iexact Hown
        simp only [hty, ↓reduceIte]
        wp_auto
        wp_for_post
        iapply HΦ; iright
        isplitr
        · ipureintro; exact Hen
        iexists d; iexact Hown
      wp_for_post
      iapply HΦ; iright
      isplitr
      · ipureintro; exact Hen
      iexists d; iexact Hown
    · exact absurd rfl Hen

end heap
end Perennial.github_com.imdea_software.swiftpaxos_epaxos

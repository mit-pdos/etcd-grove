/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/gob/Decoder__Decode.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The proof of `Spec/gob/Decoder__Decode.lean` (over `getCodec`'s spec, the kit's codec
obligations, and `io.ReadFull`'s harness spec).
-/
module

public import Dsverify.Proof.encoding.gob.getCodec
public import Dsverify.Spec.encoding.gob.Decoder__Decode
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.Bytes

@[expose] public section

noncomputable section

namespace Perennial.encoding.gob

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The header's word after `i` of the 8 loop iterations. -/
def orAcc (bs : List w8) (i : Nat) : w64 :=
  (List.range i).foldl (fun n j => n ||| (W64 (uint.Z (bs.getD j (W8 0))) <<< (W64 8 * W64 j))) (W64 0)

theorem orAcc_succ (bs : List w8) (i : Nat) :
    orAcc bs (i + 1) = orAcc bs i ||| (W64 (uint.Z (bs.getD i (W8 0))) <<< (W64 8 * W64 i)) := by
  simp [orAcc, List.range_succ, List.foldl_append]

theorem orAcc_eight (b0 b1 b2 b3 b4 b5 b6 b7 : w8) :
    orAcc [b0, b1, b2, b3, b4, b5, b6, b7] 8 = leToU64 [b0, b1, b2, b3, b4, b5, b6, b7] := by
  rw [← github_com.imdea_software.swiftpaxos.examples.swiftnet.leToU64_or]
  simp only [orAcc, List.range_succ, List.range_zero, List.nil_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil, List.getD_cons_zero, List.getD_cons_succ]
  simp only [BitVec.ofInt_natCast]
  simp [W64]

theorem orAcc_zero (bs : List w8) : orAcc bs 0 = W64 0 := rfl

attribute [irreducible] orAcc

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [pkgState : github_com.imdea_software.swiftpaxos.SwiftNetPkgState GF]
variable [github_com.imdea_software.swiftpaxos.examples.swiftnet.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [net.rpc.RpcKit] [net.rpc.RpcCodec GF]
variable [io.ExtraAssumptions]

/-- The 8-byte slice over `hdr[:]` is the array again. -/
theorem slice_to_array (l : Loc) (xs : List w8) :
    (slice.mk l (W64 8) (W64 8) ↦* xs : IProp GF) ⊢
      typedPointsto l (array.mk 8 xs : GoArray w8 8) (DFrac.own 1) := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, -⟩)
  · exfalso
    have := H.1
    simp [slice.nil, slice.mk] at this
  · have h8 : sint.Z (W64 8) = 8 := rfl
    simp only
    rw [h8]
    iexact H

theorem decoder_split (dec : Loc) (dq : DFrac) (rd : GoInterface) :
    (dec ↦{dq} (⟨rd⟩ : encoding.gob.Decoder) : IProp GF) ⊢
      typedPointsto (structFieldRef encoding.gob.Decoder go!"r" dec) rd dq ∗ ⌜dec ≠ null⌝ := by
  iintro Hd
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hd
  ihave H := typedPointsto_split _ _ _ $$ Hd
  simp only [TypedPointsto.typedPointstoDef]
  icases H with ⟨H, -⟩
  iframe H
  ipureintro; exact Hnn

theorem dec_combine (dec : Loc) (dq : DFrac) (rd : GoInterface) (h : dec ≠ null) :
    (typedPointsto (structFieldRef encoding.gob.Decoder go!"r" dec) rd dq : IProp GF) ⊢
      dec ↦{dq} (⟨rd⟩ : encoding.gob.Decoder) := by
  iintro H
  iapply typedPointsto_combine _ _ _ h
  simp only [TypedPointsto.typedPointstoDef]
  iframe

omit [io.ExtraAssumptions] in
/-- Loading byte `j` of the header through `IndexRef` (as `uuid`'s `wp_load_byte`). -/
theorem wp_load_hdr (p : Loc) (vs : List w8) (j : Int) (h0 : 0 ≤ j) (h1 : j < 8) :
    {{ (p ↦ (array.mk 8 vs : GoArray w8 8) : IProp GF) }}
      (App (Val (GoInstruction (GoLoad go.byte))) (Val #(arrayIndexRef w8 j p)))
    {{ RET #(vs.getD j.toNat (W8 0)); p ↦ (array.mk 8 vs : GoArray w8 8) }} := by
  wp_start as Hp
  ihave %Hlen := array_len (GF := GF) p (DFrac.own 1) 8 vs $$ Hp
  have hj : j.toNat < vs.length := by omega
  icases array_acc (GF := GF) p j (DFrac.own 1) 8 ⟨vs⟩ (vs[j.toNat]) h0
    (List.getElem?_eq_getElem hj) $$ Hp with ⟨He, Hp⟩
  wp_apply IntoValTyped.wp_load (t := go.byte) _ _ _ $$ He as He
  ihave Hp := Hp $$ %(vs[j.toNat]) [He]
  · iexact He
  simp only [List.set_getElem_self]
  rw [show vs.getD j.toNat (W8 0) = vs[j.toNat] by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]]
  iapply HΦ
  iexact Hp

set_option goose.wp.extras true in
set_option maxHeartbeats 400000 in
/-- `Decoder.Decode`'s spec, over `getCodec`'s, with the run's choice of the package state
(`hst`), and (the section's `io.ExtraAssumptions`) goose's unfolding of `io.ReadFull`, which every
node of the kit assumes (`SwiftNetSpec.nodeAssumptions`). -/
theorem Decoder.Decode.wp_proof (hst : pkgState.gob = isInit) (wp_getCodec : getCodec.spec (GF := GF)) :
    Decoder.Decode.spec (GF := GF) := by
  intro dec dq rd I R ptr D Ψ
  wp_start as ⟨#Hset, #Hok, #Hio, #Hrd, HI, Hd, HD, #Hdec⟩
  wp_auto
  icases decoder_split dec dq rd $$ Hd with ⟨r, %Hnn⟩
  ihave Hhdr := slice_array (GF := GF) hdr_ptr _ _ (by decide) $$ hdr
  wp_auto
  rw [show W64 8 - W64 0 = W64 8 from rfl, show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0]
  wp_apply (bufio.wp_ReadFull rd I R (slice.mk hdr_ptr (W64 8) (W64 8))
    (_root_.Perennial.zero_val (GoArray w8 8)).arr) $$ [$Hio $Hrd HI Hhdr]
    as %n1 %err1 ⟨%data1, %Hd1, Hhdr, HI, #He1⟩
  · iframe
  rcases err1 with ei | _
  · -- the header's read failed
    wp_auto
    ihave Hd := dec_combine dec dq rd Hnn $$ r
    iapply HΦ
    iframe Hd
    iexists data1
    iframe HI
    iright
    iunfold bufio.errOrNil at He1
    icases He1 with (%Hn | ⟨#Ha, -⟩)
    · cases Hn
    iframe Ha
    isplitr
    · ipureintro; simp
    ileft; iexact HD
  obtain ⟨-, -, Hd1⟩ := Hd1
  have hl8 : data1.length = 8 := by have h := Hd1.1 rfl; rw [h]; rfl
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ : ∃ b0 b1 b2 b3 b4 b5 b6 b7,
      data1 = [b0, b1, b2, b3, b4, b5, b6, b7] := by
    match data1, hl8 with
    | [b0, b1, b2, b3, b4, b5, b6, b7], _ => exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩
  simp only [List.length_cons, List.length_nil, List.drop_replicate, List.append_nil,
    show (8 : Nat) - (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = 0 from rfl, List.replicate_zero]
  ihave Hhdr := slice_to_array hdr_ptr _ $$ Hhdr
  wp_auto
  ihave HL : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "n" ∷ n_ptr ↦ orAcc [b0, b1, b2, b3, b4, b5, b6, b7] (uint.nat i) ∗
      "%Hi" ∷ ⌜uint.nat i ≤ 8⌝ : IProp GF) $$ [i n]
  · iexists W64 0
    rw [show uint.nat (W64 0) = 0 from rfl, orAcc_zero]
    iframe; ipureintro; decide
  wp_for HL
  wp_if_destruct
  · rw [ite_eq_left_iff.mpr (by intro h; exfalso; apply h; constructor <;> word)]
    wp_apply wp_load_hdr hdr_ptr _ (sint.Z i) (by word) (by word) $$ Hhdr as Hhdr
    wp_for_post
    iframe
    iexists i + W64 1
    have hi8 : uint.nat i < 8 := by word
    rw [show (sint.Z i).toNat = uint.nat i by word, show W64 8 * i = W64 8 * W64 (uint.nat i) by word,
      ← orAcc_succ, show uint.nat (i + W64 1) = uint.nat i + 1 by word]
    iframe
    ipureintro; omega
  · have hi : uint.nat i = 8 := by word
    rw [hi, orAcc_eight]
    ihave #Hinit := isInit_access hst $$ Hpkg
    iunfold isInit at Hinit
    icases Hinit with ⟨#HTB, -⟩
    ihave ⟨%tb, #Htb, #Htbe, %Htbne⟩ := bufio.newVar_errOrNil _ _ $$ HTB
    wp_if_destruct
    · -- a frame over `MaxFrame`: `errTooBig`
      try wp_auto
      ihave Hd := dec_combine dec dq rd Hnn $$ r
      iapply HΦ
      iframe Hd
      iexists [b0, b1, b2, b3, b4, b5, b6, b7]
      iframe HI
      iright
      iunfold bufio.errOrNil at Htbe
      icases Htbe with (%Hn | ⟨#Ha, -⟩)
      · exact absurd Hn Htbne
      iframe Ha
      isplitr
      · ipureintro; exact Htbne
      ileft; iexact HD
    have hn : uint.Z (leToU64 [b0, b1, b2, b3, b4, b5, b6, b7]) ≤ 2 ^ 30 := by word
    wp_apply (wp_slice_make2 (V := w8) (leToU64 [b0, b1, b2, b3, b4, b5, b6, b7])) as %body ⟨Hbody, Hcap⟩
    · ipureintro; word
    try wp_auto
    wp_apply (bufio.wp_ReadFull rd I (R ++ [b0, b1, b2, b3, b4, b5, b6, b7]) body
      (List.replicate (sint.nat (leToU64 [b0, b1, b2, b3, b4, b5, b6, b7])) (W8 0)))
      $$ [$Hio $Hrd HI Hbody] as %n2 %err2 ⟨%data2, %Hd2, Hbody, HI, #He2⟩
    · iframe
    rcases err2 with ei | _
    · -- the body's read failed: `io.ErrUnexpectedEOF` for `io.EOF`, else the reader's error
      ihave #He2' := He2
      iunfold bufio.errOrNil at He2'
      icases He2' with (%Hn | ⟨#Hea, %Hewf⟩)
      · cases Hn
      ihave #Hio' := io.isInit_access $$ Hio
      icases Hio' with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
      ihave ⟨%ue, #Hue, #Hueo, %Hune⟩ := bufio.newVar_errOrNil _ _ $$ HUEOF
      iunfold errors.newVar at HEOF
      icases HEOF with ⟨%eofx, #HEOF, -⟩
      wp_auto
      rw [List.append_assoc R]
      by_cases hty : ei.ty = go.GoType.PointerType errors.errorString.ty
      · obtain ⟨l, hl⟩ := Hewf ei rfl _ hty
        simp only [hty, ↓reduceIte]
        rw [hl]
        wp_auto
        wp_if_destruct
        · -- `io.EOF`: `io.ErrUnexpectedEOF`
          ihave Hd := dec_combine dec dq rd Hnn $$ r
          iapply HΦ
          iframe Hd
          iexists [b0, b1, b2, b3, b4, b5, b6, b7] ++ data2
          iframe HI
          iright
          iunfold bufio.errOrNil at Hueo
          icases Hueo with (%Hn | ⟨#Ha, -⟩)
          · exact absurd Hn Hune
          iframe Ha
          isplitr
          · ipureintro; exact Hune
          ileft; iexact HD
        try wp_auto
        ihave Hd := dec_combine dec dq rd Hnn $$ r
        iapply HΦ
        iframe Hd
        iexists [b0, b1, b2, b3, b4, b5, b6, b7] ++ data2
        iframe HI
        iright
        iframe Hea
        isplitr
        · ipureintro; simp
        ileft; iexact HD
      · simp only [hty, ↓reduceIte]
        wp_auto
        ihave Hd := dec_combine dec dq rd Hnn $$ r
        iapply HΦ
        iframe Hd
        iexists [b0, b1, b2, b3, b4, b5, b6, b7] ++ data2
        iframe HI
        iright
        iframe Hea
        isplitr
        · ipureintro; simp
        ileft; iexact HD
    obtain ⟨-, -, Hd2⟩ := Hd2
    have hl2 : data2.length = sint.nat (leToU64 [b0, b1, b2, b3, b4, b5, b6, b7]) := by
      have h := Hd2.1 rfl; simpa using h
    simp only [hl2, List.drop_replicate, Nat.sub_self, List.replicate_zero,
      List.append_nil]
    wp_auto
    wp_apply wp_getCodec $$ [$Hset] as %c #Hfns
    unfold codecFns
    icases Hfns with ⟨-, #HDf⟩
    unfold net.rpc.kitCodecOk
    icases Hok with ⟨-, #HdecOk, -⟩
    unfold net.rpc.decOk
    wp_auto
    ihave Hdd := Hdec $$ HD
    ispecialize Hdd $$ %data2
    wp_apply HdecOk $$ Hbody Hdd as %err %ok Hbody %Hok' %Hnse HΨ Hmsg
    try wp_auto
    ihave Hd := dec_combine dec dq rd Hnn $$ r
    have hgf : [b0, b1, b2, b3, b4, b5, b6, b7] ++ data2 =
        github_com.imdea_software.swiftpaxos.sp.gobFrame data2 := by
      simp only [github_com.imdea_software.swiftpaxos.sp.gobFrame]
      rw [hl2, show (W64 ((sint.nat (leToU64 [b0, b1, b2, b3, b4, b5, b6, b7]) : Nat) : Int)) =
        leToU64 [b0, b1, b2, b3, b4, b5, b6, b7] by word, leToU64_le _ rfl]
    rw [List.append_assoc R, hgf]
    iapply HΦ
    iframe Hd
    iexists github_com.imdea_software.swiftpaxos.sp.gobFrame data2
    iframe HI
    cases ok
    · iright
      have hne : err ≠ interface.nil := fun h => by simpa using Hok'.1 h
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hmsg with ⟨%msg, #Hm⟩
      isplitr
      · ipureintro; exact hne
      isplitr
      · iapply net.rpc.errMsg_errAny; iexact Hm
      iright
      iexists data2
      iframe HΨ
      ipureintro; rfl
    · ileft
      isplitr
      · ipureintro; exact Hok'.2 rfl
      iexists data2
      iframe HΨ
      ipureintro
      refine ⟨rfl, ?_⟩
      rw [hl2]; word

end proof

end Perennial.encoding.gob

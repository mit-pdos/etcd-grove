/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/BufRead.lean`, run
`rabia-r1wake-1`, onto the revised bufio: the lab's `bufioReadsOk` and harness `wp_ReadFull` are
Perennial's `io.ReadFull` over the reader's own contract, `bufio.ownBufReader_readerOk`
(`wp_ReadFull_buf`); the lab's `MsgPkgDeps` is the package fact `msgFact`.)

`message.BufRead`'s proof: two `io.ReadFull`s through the `*bufio.Reader`, the length from the 4
little-endian bytes (`leToU32`); longer than `data`: `errFrameTooLarge` (N6); otherwise `data[:n2]`
is in range and `ReadFull` fills it exactly (the header and the payload make `frame`,
`frame_of_header`).
-/
module

public import Dsverify.Proof.rabia.internal.message.FrameDeps
public import Proof.bufio.ReaderLaws
public import Spec.bufio.Reader__ReadOk
public import Dsverify.Proof.rabia.internal.message.SpecInternal
public import Perennial.Proof.io.Link

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.message

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions]
variable (wp_ReadOk : EtcdGrove.bufio.Reader.Read.specOk (GF := GF) (hG := hG))
include wp_ReadOk

/-- `io.ReadFull(reader, buf)` through a `*bufio.Reader` (the lab's `wp_ReadFull` over
`bufioReadsOk`): Perennial's `io.ReadFull` over the reader's contract
(`bufio.ownBufReader_readerOk`); an error exactly when the buffer is not filled (`io.EOF` and
`io.ErrUnexpectedEOF` are non-`nil`). -/
theorem wp_ReadFull_buf (br : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (R : List w8) (buf : GoSlice) (bs : List w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗
        EtcdGrove.bufio.ownBufReader br ri connPre S E R ∗ buf ↦* bs }}
      (App (App (Val (@! _root_.Perennial.io.ReadFull))
        (Val #(interface.mkOk (go.GoType.PointerType _root_.Perennial.bufio.Reader.ty) #br)))
        (Val #buf))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ∃ data : List w8, ⌜n = W64 data.length ∧ data.length ≤ bs.length ∧
          (err = interface.nil ↔ data.length = bs.length)⌝ ∗
        buf ↦* (data ++ bs.drop data.length) ∗
        EtcdGrove.bufio.ownBufReader br ri connPre S E (R ++ data) }} := by
  iintro %Φ ⟨#Hio, Hown, Hb⟩ HΦ
  have hR := EtcdGrove.bufio.ownBufReader_readerOk (GF := GF)
    wp_ReadOk br ri connPre S E
  have hri : EtcdGrove.bufio.readerIface br =
      ⟨go.GoType.PointerType _root_.Perennial.bufio.Reader.ty, #br⟩ := rfl
  rw [hri] at hR
  ihave #Hrok := hR
  ihave #Hi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, #HEOF, #HUEOF, -⟩
  iunfold _root_.Perennial.errors.newVar at HEOF HUEOF
  icases HEOF with ⟨%x1, #Heof, -⟩
  icases HUEOF with ⟨%x2, #Hueof, -⟩
  iapply _root_.Perennial.io.wp_ReadFull ⟨go.GoType.PointerType _root_.Perennial.bufio.Reader.ty, #br⟩
    (fun R m => 0 < m → connPre R m) (EtcdGrove.bufio.ownBufReader br ri connPre S E)
    (EtcdGrove.bufio.errE E) R buf bs _ _
    $$ [Hown Hb]
  · iframe Hio Hrok Heof Hueof Hown Hb
    ipureintro
    intro ys _ h; exact h
  inext
  iintro %n %err ⟨%ys, %Hys, Hb, Hown, #Hres⟩
  unfold _root_.Perennial.io.readFullRes
  ihave %Hiff : ⌜err = interface.nil ↔ ys.length = bs.length⌝ $$ [Hres]
  · icases Hres with (%h | ⟨%e, %h, -⟩)
    · ipureintro; exact ⟨fun _ => h.1, fun _ => h.2⟩
    · ipureintro
      obtain ⟨hlt, hne, h1, h2⟩ := h
      refine ⟨fun he => ?_, fun hl => absurd hl (by omega)⟩
      by_cases hc : e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x1 ∧ ys ≠ []
      · rw [h1 hc] at he; simp [interface.mkOk] at he
      · rw [h2 hc] at he; exact absurd he hne
  iapply HΦ
  iexists ys
  iframe Hb Hown
  ipureintro
  refine ⟨?_, Hys.2, Hiff⟩
  apply BitVec.eq_of_toInt_eq
  show sint.Z n = sint.Z (W64 (ys.length : Int))
  rw [← Hys.1]
  word


set_option maxHeartbeats 1000000 in
theorem BufRead.wp_proofB : BufRead.specB (GF := GF) := by
  intro br ri S E R sl ds
  wp_start as ⟨Hown, Hsl⟩
  ihave ⟨#Hpb, #Hpio, #Hpbin⟩ := msgPkgDeps_get $$ Hpkg
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 4)) as %lb ⟨Hlb, -⟩
  · ipureintro; decide
  wp_apply wp_ReadFull_buf wp_ReadOk br ri S E R lb _ $$ [$Hpio $Hown $Hlb] as %n1 %err1 ⟨%d1, %Hd1, Hlb, Hown⟩
  obtain ⟨rfl, hd1l, hd1e⟩ := Hd1
  simp only [List.length_replicate] at hd1l hd1e
  wp_if_destruct
  · have hl4 : d1.length = 4 := by
      have := congrArg (fun w : w64 => w.toNat) Hif
      simp at this; omega
    have he : err1 = interface.nil := hd1e.2 hl4
    subst he
    wp_auto
    wp_apply encoding.binary.wp_LittleEndian_Uint32 lb d1 _ _ hl4 $$ [$Hlb] as Hlb
    have hc : (leToU32 d1).toNat = LittleEndian.combine d1 := leToU32_toNat d1 hl4
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
    have hL : uint.Z (leToU32 d1) = (LittleEndian.combine d1 : Int) := by
      show ((leToU32 d1).toNat : Int) = _; rw [hc]
    have hdl : (ds.length : Int) = sint.Z sl.len := by
      rw [Hlen.1]; exact Int.toNat_of_nonneg Hlen.2
    have hL32 : (LittleEndian.combine d1 : Int) < 2 ^ 32 := by
      have := (leToU32 d1).isLt; omega
    have hW : uint.Z (W64 (uint.Z (leToU32 d1))) = LittleEndian.combine d1 := by
      rw [hL]; word
    have hsl : uint.Z sl.len = ds.length := by rw [hdl]; word
    wp_if_destruct
    · -- the frame is longer than the buffer: `errFrameTooLarge`
      ihave ⟨%ef, #Hef, %Hefn⟩ := msgPkgDeps_err $$ Hpkg
      wp_auto
      iapply HΦ
      iright
      isplitr
      · ipureintro; exact Hefn
      iexists R ++ d1, ds
      iframe Hsl Hown
      ipureintro; exact List.prefix_append _ _
    have Hbnd : LittleEndian.combine d1 ≤ ds.length := by
      rw [hW, hsl] at Hif; omega
    have hk : sint.Z (W64 (uint.Z (leToU32 d1))) = LittleEndian.combine d1 := by
      rw [hL]; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hk]; simp, by omega⟩)]
    have hkn : sint.nat (W64 (uint.Z (leToU32 d1))) = LittleEndian.combine d1 := by
      have h2 := hk; simp only [sint.Z] at h2; simp only [sint.nat]; rw [h2]; simp
    ihave ⟨Hs1, Hs2⟩ := (ownSlice_split_all (W64 (uint.Z (leToU32 d1))) sl _ ds
      ⟨by omega, by omega⟩).1 $$ Hsl
    rw [hkn]
    wp_apply wp_ReadFull_buf wp_ReadOk br ri S E (R ++ d1) _ _ $$ [$Hpio $Hown $Hs1]
      as %n3 %err3 ⟨%d2, %Hd2, Hs1, Hown⟩
    obtain ⟨rfl, hd2l, hd2e⟩ := Hd2
    have htl : (List.take (LittleEndian.combine d1) ds).length = LittleEndian.combine d1 := by
      simp; omega
    rw [htl] at hd2l hd2e
    rcases err3 with ei | _
    · -- the second read failed
      wp_auto
      iapply HΦ
      iright
      isplitr
      · ipureintro; simp
      iexists R ++ d1 ++ d2, _
      ihave Hsl := slice_rejoin sl _ _ _ _ ⟨by omega, by omega⟩ (by rw [hkn]; simp; omega) $$ [$Hs1 $Hs2]
      iframe Hown Hsl
      ipureintro; rw [List.append_assoc]; exact List.prefix_append _ _
    have hd2 : d2.length = LittleEndian.combine d1 := hd2e.1 rfl
    wp_auto
    have heq : W64 (uint.Z (leToU32 d1)) = W64 d2.length := by rw [hL, hd2]
    wp_if_destruct
    · iapply HΦ
      ileft
      isplitr
      · ipureintro; rfl
      iexists d2
      have hfr : R ++ d1 ++ d2 = R ++ model.frame d2 := by
        rw [List.append_assoc, frame_of_header d1 d2 hl4 hd2]
      rw [hfr]
      have hnil : List.drop d2.length (List.take (LittleEndian.combine d1) ds) = [] := by
        simp; omega
      rw [hnil, List.append_nil]
      ihave Hsl := slice_rejoin sl _ _ _ _ ⟨by omega, by omega⟩ (by rw [hkn]; omega) $$ [$Hs1 $Hs2]
      rw [← hd2]
      iframe Hown Hsl
      ipureintro; exact ⟨rfl, by omega, by omega⟩
    exfalso; exact Hif heq
  have hne : err1 ≠ interface.nil := by
    intro h; apply Hif; rw [hd1e.1 h]; rfl
  iapply HΦ
  iright
  isplitr
  · ipureintro; exact hne
  iexists R ++ d1, ds
  iframe Hsl Hown
  ipureintro; exact List.prefix_append _ _

theorem BufRead.wp_proof : BufRead.spec (GF := GF) := by
  intro br ri S E R sl ds
  iintro %Φ Hpre HΦ
  iapply (BufRead.wp_proofB wp_ReadOk br ri S E R sl ds) $$ Hpre
  inext
  iintro %n %e Hres
  iapply HΦ
  icases Hres with (⟨%He, %bs, %Hbs, Hsl, Hown⟩ | Hres)
  · ileft
    isplitr
    · ipureintro; exact He
    iexists bs
    iframe Hsl Hown
    ipureintro; exact ⟨Hbs.1, Hbs.2.1⟩
  iright
  iexact Hres

end proof

end Perennial.rabia.internal.message

/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/message/BufWrite.lean`, run
`rabia-r1wake-1`, onto the revised bufio: `bufio.Writer.Write.spec`'s seven-part answer.)

`message.BufWrite`'s proof: the header (`PutUint32` of the length) and the data, two
`(*bufio.Writer).Write`s; the header's write is allowed by `Q`'s prefix closure
(`io.streamWriterOk_prefixClosed`). `BufWrite.wp_tooLong`: data of `2^32` bytes or more (N8), the error
`errFrameTooLong`, nothing written.
-/
module

public import Dsverify.Proof.rabia.internal.message.FrameDeps
public import Spec.bufio.Writer__Write
public import Dsverify.Proof.rabia.internal.message.SpecInternal

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.message

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]
variable [_root_.Perennial.bufio.Assumptions]

/-- `Q` holds of a prefix of a stream it holds of (a prefix-closed `Q`, `io.prefixClosed`). -/
theorem Q_of_prefix (Q : List w8 → IProp GF) (x y : List w8) (h : x <+: y) :
    EtcdGrove.io.prefixClosed Q ⊢ □ Q y -∗ □ Q x := by
  obtain ⟨z, rfl⟩ := h
  iintro #Hpc #HQ
  unfold EtcdGrove.io.prefixClosed
  imodintro
  iapply Hpc $$ %x %z HQ

set_option maxHeartbeats 1000000 in
theorem BufWrite.wp_proof (wp_Write : EtcdGrove.bufio.Writer.Write.spec (GF := GF) (hG := hG)) :
    BufWrite.spec (GF := GF) := by
  intro bw wi J Q Ew sz sent pend err sl dq bs
  wp_start as ⟨%hbs, #Hwr, Hown, #HQ, Hsl⟩
  ihave ⟨#Hpb, #Hpio, #Hpbin⟩ := msgPkgDeps_get $$ Hpkg
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_if_destruct
  · exfalso
    have h1 : uint.Z sl.len = sint.Z sl.len := by word
    have h2 : uint.Z (W64 4294967295) = 4294967295 := rfl
    have h3 : ((sint.nat sl.len : Nat) : Int) = sint.Z sl.len := Int.toNat_of_nonneg Hlen.2
    omega
  wp_apply (wp_slice_make2 (V := w8) (W64 4)) as %lb ⟨Hlb, -⟩
  · ipureintro; decide
  have hn : (W32 (sint.Z sl.len)).toNat = bs.length := by
    have h1 : sint.Z sl.len = (bs.length : Int) := by rw [Hlen.1]; exact (Int.toNat_of_nonneg Hlen.2).symm
    rw [h1]; simp [W32]; omega
  have hfr := u32Le_frame bs _ hn
  wp_apply encoding.binary.wp_LittleEndian_PutUint32 lb (List.replicate 4 (zero_val w8)) [] _ (by simp) $$ [Hlb] as Hlb
  · simp only [List.append_nil]; iexact Hlb
  ihave #Hpc := EtcdGrove.io.streamWriterOk_prefixClosed wi J Q Ew $$ Hwr
  ihave #HQ1 := Q_of_prefix Q (sent ++ pend ++ u32Le (W32 (sint.Z sl.len))) _
    (by rw [← hfr, ← List.append_assoc]; exact List.prefix_append _ _) $$ Hpc HQ
  rw [List.append_nil]
  wp_apply wp_Write bw wi J Q Ew sz sent pend err lb _ _ $$ [$Hown $Hlb]
    as %nn1 %e1 ⟨%k1, %sent1, %pend1, %Hk1, Hlb, Hown⟩
  · iintro -; iexact HQ1
  have hl4 : (u32Le (W32 (sint.Z sl.len))).length = 4 := u32Le_length _
  obtain ⟨rfl, hk1l, hk1s, hk1p, hk1e, -, -⟩ := Hk1
  rw [hl4] at hk1l hk1e
  rcases e1 with ei | _
  · -- the length's write failed
    wp_auto
    iapply HΦ
    iexists k1, sent1, pend1
    iframe Hsl Hown
    ipureintro
    rw [← hfr, List.take_append_of_le_length (by omega)]
    refine ⟨by simp; omega, hk1s, hk1p, fun h => by cases h⟩
  have hk1 : k1 = 4 := hk1e rfl
  subst hk1
  wp_auto
  have HQ2 : sent1 ++ pend1 ++ bs = sent ++ pend ++ model.frame bs := by
    rw [hk1s, ← hfr, List.take_of_length_le (by omega)]; simp
  ihave #HQ2' : □ Q (sent1 ++ pend1 ++ bs) $$ []
  · rw [HQ2]; iexact HQ
  wp_apply wp_Write bw wi J Q Ew sz sent1 pend1 _ sl _ _ $$ [$Hown $Hsl]
    as %nn2 %e2 ⟨%k2, %sent2, %pend2, %Hk2, Hsl, Hown⟩
  · iintro -; iexact HQ2'
  obtain ⟨rfl, hk2l, hk2s, hk2p, hk2e, -, -⟩ := Hk2
  rcases e2 with ei | _
  · -- the data's write failed
    wp_auto
    iapply HΦ
    iexists 4 + k2, sent2, pend2
    iframe Hsl Hown
    ipureintro
    rw [← hfr, List.take_append, List.take_of_length_le (by omega), hk2s, hk1s,
      List.take_of_length_le (by omega)]
    refine ⟨by simp; omega, ?_, hk1p.trans hk2p, fun h => by cases h⟩
    simp [hl4]
  have hk2 : k2 = bs.length := hk2e rfl
  subst hk2
  wp_auto
  have heq : W64 (bs.length : Int) = sl.len := by
    apply BitVec.eq_of_toInt_eq
    have h1 : sint.Z sl.len = (bs.length : Int) := by
      rw [Hlen.1]; exact (Int.toNat_of_nonneg Hlen.2).symm
    show sint.Z (W64 (bs.length : Int)) = sint.Z sl.len
    rw [h1]; word
  wp_if_destruct
  · iapply HΦ
    iexists 4 + bs.length, sent2, pend2
    iframe Hsl Hown
    ipureintro
    rw [← hfr, List.take_of_length_le (by simp; omega), hk2s, hk1s,
      List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    refine ⟨by simp [hl4], by simp, hk1p.trans hk2p, fun _ => by simp [hl4]⟩
  exfalso; exact Hif heq

/-- `BufWrite` on data of `2^32` bytes or more (N8): a non-nil error, nothing written (the writer
is not touched). -/
theorem BufWrite.wp_proofTooLong : BufWrite.specTooLong (GF := GF) := by
  intro bw sl dq bs
  intro hbs
  wp_start as Hsl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave ⟨%e, #He, %Hen⟩ := errFrameTooLong_get $$ Hpkg
  wp_auto
  wp_if_destruct
  · iapply HΦ
    iframe Hsl
    ipureintro; exact Hen
  exfalso
  have h1 : uint.Z sl.len = sint.Z sl.len := by word
  have h2 : uint.Z (W64 4294967295) = 4294967295 := rfl
  have h3 : ((sint.nat sl.len : Nat) : Int) = sint.Z sl.len := Int.toNat_of_nonneg Hlen.2
  omega

end proof

end Perennial.rabia.internal.message

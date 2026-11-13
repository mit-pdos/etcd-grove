/- Lean-first (no Rocq counterpart).
# Lemmas of the WAL decoder's vocabulary (W3a of `notes/wal-fsext-plan.md`)

What the proof of `decoder.decodeRecord` uses of `DecDefs`:
* `fbr_readerStream`: a decoder's `*fileutil.FileBufReader`, converted to `io.Reader`, reads its
  file's bytes as a stream (over `FileBufReader.Read`'s spec), its state the `*bufio.Reader`'s;
* `ownReader_prefix`: what a file's reader has delivered is a prefix of the file's bytes.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.DecDefs
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader__Read

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open WalEnc

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- A pure consequence, keeping what it was derived from. -/
theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ ⌜φ⌝ ∗ P :=
  (BI.and_intro h .rfl).trans BI.persistent_and_sep_mp

/-- See the file header. -/
theorem ownReader_prefix (IoE : GoInterface → Prop) (eof : GoInterface) (F : DecFile GF) (b : Loc)
    (E : List w8 → GoInterface → Prop) (r : List w8) :
    decFile IoE eof F ∗ bufio.ownReader b F.fr F.S E r ⊢
      ⌜r <+: F.bs⌝ ∗ bufio.ownReader b F.fr F.S E r := by
  refine (keep_pure ?_).trans (BI.sep_mono_right BI.sep_elim_right)
  iintro ⟨#HF, Hb⟩
  iunfold decFile at HF
  icases HF with ⟨-, #Hpre, -⟩
  iunfold bufio.ownReader at Hb
  icases Hb with ⟨-, %v, %bs, -, -, -, HS, -⟩
  ihave %h := Hpre $$ HS
  ipureintro
  exact (List.prefix_append _ _).trans h

/-- See the file header. -/
theorem fbr_readerStream
    (HRead : go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.Read.spec (GF := GF) (hG := hG))
    (IoE : GoInterface → Prop) (eof : GoInterface) (F : DecFile GF) (fbr b : Loc)
    (fi err : GoInterface) :
    (fbr ↦□ go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.mk b fi err : IProp GF) ∗
      decFile IoE eof F ⊢
      io.readerStream ⟨go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.ty, #fbr⟩
        (bufio.ownReader b F.fr F.S (decRdErr F.bs eof IoE)) (decRdErr F.bs eof IoE) := by
  iintro ⟨#Hf, #HF⟩
  iunfold decFile at HF
  icases HF with ⟨#Hrs, -⟩
  iunfold io.readerStream
  imodintro
  iintro %r %p %xs
  imodintro
  iintro %Φ ⟨Hb, Hp⟩ HΦ
  wp_apply HRead fbr b fi err DFrac.discard F.fr F.S (decRdErr F.bs eof IoE) r p xs $$ Hrs
    [Hb Hp] as %n %e ⟨%ys, %Hys, Hp, -, Hb⟩
  · iframe
    iexact Hf
  iapply HΦ
  iexists ys
  iframe
  ipureintro
  exact Hys

/-- The readers, the files and what they delivered are lists of the same length. -/
theorem ownFbrs_len (IoE : GoInterface → Prop) (eof : GoInterface) :
    ∀ (fbrs : List Loc) (fs : List (DecFile GF)) (rs : List (List w8)),
    ownFbrs IoE eof fbrs fs rs ⊢ ⌜fbrs.length = fs.length ∧ fs.length = rs.length⌝
  | [], [], [] => by iintro -; ipureintro; simp
  | b :: bs, G :: gs, q :: qs => by
    simp only [ownFbrs]
    iintro ⟨-, H⟩
    ihave %h := ownFbrs_len IoE eof bs gs qs $$ H
    ipureintro
    simp [h.1, h.2]
  | [], _ :: _, _ | _ :: _, [], _ | _, [], _ :: _ | _, _ :: _, [] => by
    simp only [ownFbrs]; exact BI.false_elim

end lemmas

/-! ## Pure: the decoder's step by what the reads returned -/

section pure
variable [GooseExts]

/-- What a short `ReadFull` from a file's reader (`decRdErr`) says, when its error is not one of
`IoE`: the reader reached the end of the bytes, and the error is `io.EOF` if nothing came, else
`io.ErrUnexpectedEOF`. -/
theorem readFull_short {bs r ys : List w8} {m : Nat} {eof ueof err : GoInterface}
    {IoE : GoInterface → Prop} (h : io.readFullOk (decRdErr bs eof IoE) eof ueof r ys m err)
    (hio : ¬ IoE eof) (hnil : err ≠ GoInterface.nil) (hnI : ¬ IoE err) :
    ys.length < m ∧ r ++ ys = bs ∧ ((err = eof ∧ ys = []) ∨ (err = ueof ∧ ys ≠ [])) := by
  rcases h with ⟨_, h⟩ | ⟨hlt, e, _, hE, h1, h2⟩
  · exact absurd h hnil
  · by_cases hc : e = eof ∧ ys ≠ []
    · rcases hE with ⟨hr, _⟩ | hI
      · exact ⟨hlt, hr, Or.inr ⟨h1 hc, hc.2⟩⟩
      · exact absurd (hc.1 ▸ hI) hio
    · rw [h2 hc] at hnI ⊢
      rcases hE with ⟨hr, he⟩ | hI
      · refine ⟨hlt, hr, Or.inl ⟨he, ?_⟩⟩
        by_cases hy : ys = []
        · exact hy
        · exact absurd ⟨he, hy⟩ hc
      · exact absurd hI hnI

/-- The errors a `ReadFull` from a file's reader returns. -/
theorem readFull_err_cases {bs r ys : List w8} {m : Nat} {eof ueof err : GoInterface}
    {IoE : GoInterface → Prop} (h : io.readFullOk (decRdErr bs eof IoE) eof ueof r ys m err) :
    err = GoInterface.nil ∨ err = eof ∨ err = ueof ∨ IoE err := by
  rcases h with ⟨_, h⟩ | ⟨_, e, _, hE, h1, h2⟩
  · exact Or.inl h
  · by_cases hc : e = eof ∧ ys ≠ []
    · exact Or.inr (Or.inr (Or.inl (h1 hc)))
    · rw [h2 hc]
      rcases hE with ⟨_, he⟩ | hI
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (Or.inr hI))

/-- What follows the delivered prefix `bs.take off` in `bs`. -/
theorem take_append_prefix {bs ys : List w8} {off : Nat} (hp : bs.take off ++ ys <+: bs)
    (hne : ys ≠ []) : off + ys.length ≤ bs.length ∧ ys <+: bs.drop off := by
  obtain ⟨t, ht⟩ := hp
  have hlen := congrArg List.length ht
  simp only [List.length_append, List.length_take] at hlen
  have hy : 0 < ys.length := List.length_pos_iff.mpr hne
  have hoff : off ≤ bs.length := by omega
  refine ⟨by rw [Nat.min_eq_left hoff] at hlen; omega, ?_⟩
  refine ⟨t, ?_⟩
  conv => rhs; rw [← ht]
  rw [List.append_assoc, List.drop_left' (by simp [Nat.min_eq_left hoff])]

theorem take_append_eq {bs ys : List w8} {off : Nat} (h : bs.take off ++ ys = bs)
    (hne : ys ≠ []) : off + ys.length = bs.length ∧ bs.drop off = ys := by
  have hlen := congrArg List.length h
  simp only [List.length_append, List.length_take] at hlen
  have hy : 0 < ys.length := List.length_pos_iff.mpr hne
  have hoff : off ≤ bs.length := by omega
  refine ⟨by rw [Nat.min_eq_left hoff] at hlen; omega, ?_⟩
  conv => lhs; rw [← h]
  rw [List.drop_left' (by simp [Nat.min_eq_left hoff])]

theorem decodeFrameSize_fst_lt (l : w64) : (decodeFrameSize l).1 < 2 ^ 56 := by
  simp only [decodeFrameSize]
  have hm : (~~~(0xff#64 <<< 56) : w64).toNat = 2 ^ 56 - 1 := by decide
  have : (l &&& ~~~(0xff#64 <<< 56)).toNat < 2 ^ 56 := by
    rw [BitVec.toNat_and, hm]
    have := @Nat.and_le_right l.toNat (2 ^ 56 - 1)
    omega
  exact this

theorem decodeFrameSize_snd_lt (l : w64) : (decodeFrameSize l).2 < 8 := by
  simp only [decodeFrameSize]
  split
  · have : ((l >>> 56) &&& 7#64).toNat ≤ 7 := by
      rw [BitVec.toNat_and]; exact Nat.and_le_right
    show ((l >>> 56) &&& 7#64).toNat < 8
    omega
  · omega

/-- The rest of `decRecStep` once the frame's data `data` is read. -/
def decRecData (C : WalCodec) (last : Bool) (off : Nat) (c : w32) (rb pad : Nat)
    (data : List w8) : RecStep :=
  match C.decRec (data.take rb) with
  | none => .stop (.badRec (isTorn last off data)) c
  | some r =>
    if r.typ ≠ crcType then
      if r.crc = C.crc32c c r.data then .accept r (8 + rb + pad) (C.crc32c c r.data)
      else .stop (.crcErr (isTorn last off data)) (C.crc32c c r.data)
    else .accept r (8 + rb + pad) c

theorem decRecStep_end {C : WalCodec} {last : Bool} {bs : List w8} {off : Nat} {c : w32}
    (h : bs.length ≤ off) : decRecStep C last bs off c = .eof := by
  unfold decRecStep
  simp [List.length_drop, show bs.length - off = 0 by omega]

theorem decRecStep_shortLen {C : WalCodec} {last : Bool} {bs : List w8} {off : Nat} {c : w32}
    (h1 : 0 < (bs.drop off).length) (h2 : (bs.drop off).length < 8) :
    decRecStep C last bs off c = .stop .shortLen c := by
  unfold decRecStep
  simp only
  rw [if_neg (by omega), if_pos h2]

theorem decRecStep_zero {C : WalCodec} {last : Bool} {bs : List w8} {off : Nat} {c : w32}
    (h1 : 8 ≤ (bs.drop off).length) (h : leToU64 ((bs.drop off).take 8) = 0#64) :
    decRecStep C last bs off c = .eof := by
  unfold decRecStep
  simp only
  rw [if_neg (by omega), if_neg (by omega), if_pos h]

theorem decRecStep_frame {C : WalCodec} {last : Bool} {bs : List w8} {off : Nat} {c : w32}
    (h1 : 8 ≤ (bs.drop off).length) (h : leToU64 ((bs.drop off).take 8) ≠ 0#64) :
    decRecStep C last bs off c =
      let l := leToU64 ((bs.drop off).take 8)
      let rb := (decodeFrameSize l).1
      let pad := (decodeFrameSize l).2
      if bs.length < off + pad + rb then .stop .tooLarge c
      else if (bs.drop off).length < 8 + rb + pad then .stop .shortData c
      else decRecData C last off c rb pad (((bs.drop off).drop 8).take (rb + pad)) := by
  unfold decRecStep decRecData
  simp only
  rw [if_neg (by omega), if_neg (by omega), if_neg h]
  rfl

end pure

end WalFs
end EtcdGrove
end Perennial

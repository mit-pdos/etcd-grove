/-
Package `proxy`: what `connectionListener`'s buffered reader knows of the bytes it returned
(`NetFrames.lean`'s parsing over `recv_frames`): after the handshake and whole frames `A`, the next
byte is a frame's code `1` (`reader_code`); the next 8 bytes are a length below `2^63`
(`reader_len`: `Unmarshal`'s premise); a whole frame read is the next batch of the stream, with its
registration and ticket (`reader_frame`).
-/
module

public import Dsverify.Proof.raxos.Proxy.NetUnmarshal

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- The stream after the handshake and the frames `A`, then `x`, is a prefix of the port's
stream of `L`: `x` is a prefix of the frames after `A`. -/
theorem after_frames {n : Nat} (A L : List Batch) (x : List w8)
    (hA : ∀ b ∈ A, (encBatch b).length < 2 ^ 63)
    (hL : ∀ b ∈ L, batchOk b ∧ (encBatch b).length < 2 ^ 63)
    (h : hs n ++ frs A ++ x <+: hs n ++ frs L) :
    frs A = frs (L.take A.length) ∧ x <+: frs (L.drop A.length) := by
  rw [List.append_assoc, List.prefix_append_right_inj] at h
  exact frs_align A L x (fun b hb => by have := hA b hb; omega)
    (fun b hb => by have := (hL b hb).2; omega) h

/-- The code byte after the handshake and whole frames is `1` (from what the reader has
returned, `net.connReader_proto`'s fact). -/
theorem reader_code (γ : QNames) (k n : Nat) (cid : Nat)
    (A : List Batch) (c : w8) (hA : ∀ b ∈ A, (encBatch b).length < 2 ^ 63) :
    protoPrefix (proxyInProto (GF := GF) γ k) cid (hs n ++ frs A ++ [c]) ⊢ ⌜c = W8 1⌝ := by
  iintro HI
  ihave Hp := recv_frames γ k n cid _ (by simp only [List.append_assoc]; exact List.prefix_append _ _) $$ HI
  icases Hp with (%h | ⟨%L, %hL, -⟩)
  · simp at h
  have h2 : hs n ++ frs A ++ [c] <+: hs n ++ frs L := hL.1
  obtain ⟨-, h3⟩ := after_frames A L _ hA hL.2 h2
  obtain ⟨b', -, hc, -⟩ := frs_head L A.length c [] h3
  ipureintro; exact hc

/-- The length after a frame's code byte is below `2^63` (`unmarshalB`'s bound, at the stream's
fact `protoPrefix`). -/
theorem reader_len (γ : QNames) (k n : Nat) (cid : Nat) (A : List Batch)
    (hA : ∀ b ∈ A, (encBatch b).length < 2 ^ 63) :
    ⊢@{IProp GF} □ (∀ d, protoPrefix (proxyInProto γ k) cid ((hs n ++ frs A ++ [W8 1]) ++ d) -∗
      ⌜d.length = 8 → leNum d < 2 ^ 63⌝) := by
  iintro !> %d HI
  ihave Hp := recv_frames γ k n cid _ (by simp only [List.append_assoc]; exact List.prefix_append _ _) $$ HI
  icases Hp with (%h | ⟨%L, %hL, -⟩)
  · simp at h
  ipureintro
  intro hd
  have h2 : hs n ++ frs A ++ (W8 1 :: d) <+: hs n ++ frs L := by
    simpa [List.append_assoc] using hL.1
  obtain ⟨-, h3⟩ := after_frames A L _ hA hL.2 h2
  obtain ⟨b', hb', -, h4⟩ := frs_head L A.length _ _ h3
  have h5 := prefix_le8 (e := []) hd (by rw [List.append_nil, List.append_assoc] at *; exact h4)
  have hb'L := (hL.2 b' (List.mem_of_getElem? hb')).2
  rw [h5, leNum_le8 _ (by omega)]
  exact hb'L

/-- A whole frame read after the handshake and the frames `A`: its batch `b'`, registered, with
its ticket of frame number `A.length`. -/
theorem reader_frame (γ : QNames) (k n : Nat) (cid : Nat)
    (A : List Batch) (bs : List w8) (hA : ∀ b ∈ A, (encBatch b).length < 2 ^ 63)
    (hbs : bs.length < 2 ^ 63) :
    protoPrefix (proxyInProto (GF := GF) γ k) cid
        ((hs n ++ frs A ++ [W8 1]) ++ (le8 bs.length ++ bs)) ⊢
      ∃ b', ⌜encBatch b' = bs ∧ batchOk b' ∧ (encBatch b').length < 2 ^ 63 ∧
          (hs n ++ frs A ++ [W8 1]) ++ (le8 bs.length ++ bs) = hs n ++ frs (A ++ [b'])⌝ ∗
        batchReg γ b'.id b' ∗ ∃ c j, tixAt γ ((k : Int), c, j) cid A.length := by
  iintro HI
  ihave Hp := recv_frames γ k n cid _ (by simp only [List.append_assoc]; exact List.prefix_append _ _) $$ HI
  icases Hp with (%h | ⟨%L, %hL, #Hs⟩)
  · simp at h
  have h2 : hs n ++ frs A ++ (W8 1 :: (le8 bs.length ++ bs ++ [])) <+: hs n ++ frs L := by
    simpa [List.append_assoc] using hL.1
  obtain ⟨-, h3⟩ := after_frames A L _ hA hL.2 h2
  obtain ⟨b', hb', -, h4⟩ := frs_head L A.length _ _ h3
  have hb'L := hL.2 b' (List.mem_of_getElem? hb')
  have he : bs = encBatch b' := prefix_enc (by omega) (by omega) h4
  ihave ⟨#Hreg, #Htix⟩ := BigSepL.bigSepL_lookup hb' $$ Hs
  iexists b'
  iframe Hreg Htix
  ipureintro
  refine ⟨he.symm, hb'L.1, hb'L.2, ?_⟩
  subst he; simp [frs_append, frs_cons, frs_nil, frame, List.append_assoc]

end proofs

end Perennial.raxos

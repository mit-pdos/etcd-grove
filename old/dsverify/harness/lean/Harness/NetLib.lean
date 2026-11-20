/-
Library lemmas for proofs of programs over Go's `net` (the ergonomics pass after M2c;
`notes/harness-m2a.md`, "Ergonomics pass"):

* `ownSlice_take_acc`: a buffer `b ↦* (data ++ rest)` (what `Read` returns) gives `b[:len(data)]`
  and the way back, with the slice expression's bounds and the arithmetic of `W64 |data|`
  (no `ownSlice_split_all`/`ownSlice_combine` by hand).
* `ProtoPrefixClosed`, `protoPrefix_closed`, `recvTok_proto_closed`: for a protocol that holds of
  the empty stream and is closed under prefixes, what a reader has read meets the protocol itself
  (not only up to extension, `protoPrefix`). Framed protocols are of this form when stated as
  "whole frames, then a prefix of a frame".
* `time`: `time.Second`, `time.Millisecond`, ... are reducible values (`#(W64 …)`), so
  `wp_apply time.Time.wp_Add t _` (or `time.wp_Sleep _`) unifies the duration by itself; nothing
  needs spelling out.
-/
module

public import Harness.Proof.net.Base

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProofMode NetConn

section slices
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- `W64 n` of a length below `2^63` is `n`, signed. -/
theorem sint_Z_W64_length {n : Nat} (h : n < 2 ^ 63) : sint.Z (W64 n) = n := by
  have : ((n : Int) : w64).toInt = (n : Int) := by
    rw [BitVec.toInt_intCast]; apply Int.bmod_eq_of_le <;> omega
  exact this

/-- Split a slice holding `data ++ rest` at `len(data)`: its prefix `b[:len(data)]` holds
`data`, and gives back the whole slice. The pure facts are the bounds that the slice expression
`b[:n]` checks (`0 ≤ 0 ≤ n ≤ cap(b)`, with `n = W64 |data|`) and `W64 |data|`'s value. -/
theorem ownSlice_take_acc (b : GoSlice) (dq : DFrac) (data rest : List V) :
    (b ↦*{dq} (data ++ rest) : IProp GF) ⊢
      ⌜(0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 data.length) ∧
          sint.Z (W64 data.length) ≤ sint.Z b.cap) ∧
        sint.Z (W64 data.length) = data.length ∧ sint.nat (W64 data.length) = data.length⌝ ∗
      slice.slice b V (W64 0) (W64 data.length) ↦*{dq} data ∗
      (slice.slice b V (W64 0) (W64 data.length) ↦*{dq} data -∗ b ↦*{dq} (data ++ rest)) := by
  iintro Hb
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  ihave %Hw := ownSlice_wf _ _ _ $$ Hb
  have h63 : sint.Z b.len < 2 ^ 63 := by word
  have hlen : data.length + rest.length = (sint.Z b.len).toNat := by
    rw [← List.length_append]; exact Hl.1
  have hZ : sint.Z (W64 data.length) = data.length := sint_Z_W64_length (by omega)
  have hN : sint.nat (W64 data.length) = data.length := by
    show (sint.Z (W64 data.length)).toNat = _; rw [hZ]; rfl
  have h0 : sint.Z (W64 0) = 0 := rfl
  ihave Hsplit := (ownSlice_split_all (W64 data.length) b dq _
    ⟨by rw [hZ]; omega, by rw [hZ]; omega⟩).1 $$ Hb
  rw [hN, List.take_left' rfl, List.drop_left' rfl]
  icases Hsplit with ⟨Hpre, Hrest⟩
  isplitr
  · ipureintro; refine ⟨⟨by rw [h0]; omega, by rw [h0, hZ]; omega, by rw [hZ]; omega⟩, hZ, rfl⟩
  iframe Hpre
  iintro Hpre
  iapply ownSlice_trivial_slice_2
  iapply ownSlice_combine (W64 data.length) b dq data rest (W64 0) b.len
    ⟨by rw [hN]; rfl, by rw [h0]; omega, by rw [h0, hZ]; omega, by rw [hZ]; omega⟩ $$ Hpre Hrest

end slices

section protos
variable {GF : BundledGFunctors}

/-- A protocol that holds of the empty stream and is closed under prefixes. -/
structure ProtoPrefixClosed (P : Proto GF) : Prop where
  nil : ∀ cid, ⊢ □ P cid []
  pre : ∀ cid (a b : List w8), a <+: b → □ P cid b ⊢ □ P cid a

/-- A pure protocol `p`, true of the empty stream and closed under prefixes, is
`ProtoPrefixClosed`. -/
theorem ProtoPrefixClosed.of_pure (p : w64 → List w8 → Prop) (hnil : ∀ cid, p cid [])
    (hpre : ∀ cid a b, a <+: b → p cid b → p cid a) :
    ProtoPrefixClosed (GF := GF) (fun cid bs => iprop(⌜p cid bs⌝)) where
  nil cid := by iintro !>; ipureintro; exact hnil cid
  pre cid a b h := by iintro #%Hb; iintro !>; ipureintro; exact hpre cid a b h Hb

/-- For a prefix-closed protocol, `protoPrefix` is the protocol itself. -/
theorem protoPrefix_closed {P : Proto GF} (hP : ProtoPrefixClosed P) (cid : w64) (R : List w8) :
    protoPrefix P cid R ⊢ □ P cid R := by
  unfold protoPrefix
  iintro (%h | ⟨%ext, %h, #H⟩)
  · subst h; iapply hP.nil cid
  · iapply hP.pre cid R ext h $$ H

end protos

section recv
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- What a reader has read meets a prefix-closed protocol (`recvTok_proto` with
`protoPrefix_closed`). -/
theorem recvTok_proto_closed {P : Proto GF} (hP : ProtoPrefixClosed P) (cid : w64) (side : Side)
    (R : List w8) :
    recvTok (G := G) cid side P R ⊢ recvTok cid side P R ∗ □ P cid R := by
  iintro H
  ihave ⟨H, Hp⟩ := recvTok_proto $$ H
  iframe H
  iapply protoPrefix_closed hP $$ Hp

end recv

end Perennial

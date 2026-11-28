/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/examples/inproc/Reader__Read.lean (241f27e),
into snapstore (the `Reader` moved there: examples/snapstore/reader.go).
-/
/-
The proof of `snapstore.Reader.Read`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.snapstore.Reader__Read

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.snapstore

set_option goose.wp.extras true

theorem github_com.hashicorp.raft.examples.snapstore.Reader.Read.wp_proof :
    github_com.hashicorp.raft.examples.snapstore.Reader.Read.spec (GF := GF) (hG := hG) :=
  fun rd p buf cs eof => by
  wp_start as ⟨#Heof, Hst, Hp, %Hbuf⟩
  unfold readerSt
  icases Hst with ⟨%sl, %b, %off, #Hb, #Hsl, Hoff, %Hinv⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_if_destruct
  · iapply HΦ
    have Hcs : cs = [] := by
      rw [Hinv.2.2]; apply List.drop_eq_nil_of_le; word
    subst Hcs
    simp only [List.take_nil, List.drop_nil, List.nil_append, List.length_nil]
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0, List.drop_zero]
    iframe Hp
    isplitr
    · ipureintro; refine ⟨by decide, by omega, by simp, Or.inr ⟨trivial, rfl⟩⟩
    iexists sl, b, off
    iframe Hb Hsl Hoff
    ipureintro; exact ⟨Hinv.1, Hinv.2.1, Hinv.2.2⟩
  · ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
    rw [if_pos ⟨Hinv.1, by omega, Hwf.2⟩]
    icases (ownSlice_slice off off sl DFrac.discard b ⟨Hinv.1, Int.le_refl _, by omega⟩).1 $$ Hsl
      with ⟨-, -, Hrest⟩
    wp_auto
    rw [← Hinv.2.2]
    wp_apply wp_slice_copy p buf _ cs DFrac.discard $$ [$Hp $Hrest] as %n ⟨%Hn, Hp, -⟩
    have Hcsl : cs.length = b.length - sint.nat off := by rw [Hinv.2.2, List.length_drop]
    iapply HΦ
    have Hp_eq : cs.take buf.length ++ buf.drop cs.length =
        cs.take (sint.nat n) ++ buf.drop (sint.nat n) := by
      rw [Hn]
      rcases Nat.le_total buf.length cs.length with h | h
      · rw [Nat.min_eq_left h, List.drop_eq_nil_of_le h, List.drop_eq_nil_of_le (Nat.le_refl _)]
      · rw [Nat.min_eq_right h, List.take_of_length_le h, List.take_of_length_le (Nat.le_refl _)]
    rw [← Hp_eq]
    iframe Hp
    isplitr
    · ipureintro
      refine ⟨by word, by omega, by omega, Or.inl rfl⟩
    iexists sl, b, (off + n)
    iframe Hb Hsl Hoff
    ipureintro
    have Hsum : sint.nat (off + n) = sint.nat off + sint.nat n := by word
    refine ⟨by word, by word, ?_⟩
    rw [Hsum, Hinv.2.2, List.drop_drop]

end proof

end Perennial

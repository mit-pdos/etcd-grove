/-
The proofs of the vr kit's functions (`kit.go`, notes/dsv-vr.md), as paxos's
`examples/paxosnet/KitProof.lean`: so far `Gen` (with `digit`, `digits`).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.CodecProof
public import Perennial.Proof.github_com.goose_lang.primitive.RandomUint64

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open VsrModel VsrGhost.Impl

namespace github_com.tangledbytes.go_vsr.examples.vsrnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A decimal digit's byte. -/
def DigitB (b : w8) : Prop := 48 ≤ uint.Z b ∧ uint.Z b ≤ 57

/-- A decimal number's bytes: non-empty, at most 20 digits. -/
def DigitsB (s : GoString) : Prop := s ≠ [] ∧ s.length ≤ 20 ∧ ∀ b ∈ s, DigitB b

theorem digitB_plain {b : w8} (h : DigitB b) :
    b ≠ 32 ∧ 32 ≤ b.toNat ∧ b.toNat ≤ 126 ∧ b.toNat ≠ 34 ∧ b.toNat ≠ 92 ∧ b.toNat ≠ 60 ∧
      b.toNat ≠ 62 ∧ b.toNat ≠ 38 := by
  obtain ⟨h1, h2⟩ := h
  have e : (uint.Z b) = (b.toNat : Int) := rfl
  rw [e] at h1 h2
  refine ⟨?_, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  intro hb; subst hb; simp at h1

theorem chars_ok (s : GoString) (h : ∀ b ∈ s, DigitB b ∨ b = 107#8 ∨ b = 118#8) :
    (∀ b ∈ s, b ≠ 32) ∧ PlainStr s := by
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · rcases h b hb with h | rfl | rfl
    · exact (digitB_plain h).1
    · decide
    · decide
  · rcases h b hb with h | rfl | rfl
    · exact (digitB_plain h).2
    · decide
    · decide

theorem kin_get (d : GoString) (hd : DigitsB d ∧ d.length = 1) :
    KInOk (.get ([107#8] ++ d)) := by
  have hc := chars_ok ([107#8] ++ d) (by
    intro b hb
    rcases List.mem_append.1 hb with h | h
    · simp at h; exact .inr (.inl h)
    · exact .inl (hd.1.2.2 b h))
  refine ⟨hc, ?_, ?_⟩
  · simp only [InputBounded, List.length_append, List.length_singleton, hd.2]; omega
  · simp only [List.length_append, List.length_singleton, hd.2]; omega

theorem kin_put (d d2 ds : GoString) (hd : DigitsB d ∧ d.length = 1)
    (hd2 : DigitsB d2 ∧ d2.length = 1) (hds : DigitsB ds) :
    KInOk (.put ([107#8] ++ d) ([118#8] ++ d2 ++ ds)) := by
  have hk := chars_ok ([107#8] ++ d) (by
    intro b hb
    rcases List.mem_append.1 hb with h | h
    · simp at h; exact .inr (.inl h)
    · exact .inl (hd.1.2.2 b h))
  have hv := chars_ok ([118#8] ++ d2 ++ ds) (by
    intro b hb
    rcases List.mem_append.1 hb with h | h
    · rcases List.mem_append.1 h with h | h
      · simp at h; exact .inr (.inr h)
      · exact .inl (hd2.1.2.2 b h)
    · exact .inl (hds.2.2 b h))
  have hl := hds.2.1
  refine ⟨⟨hk, by simp, hv⟩, ?_, ?_⟩
  · simp only [InputBounded, List.length_append, List.length_singleton, hd.2, hd2.2]; omega
  · simp only [List.length_append, List.length_singleton, hd.2]; omega

theorem digitB_of (n : w64) : DigitB (W8 (uint.Z (W64 48 + n % W64 10))) := by
  unfold DigitB
  constructor <;> word

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.tangledbytes.go_vsr.examples.vsrnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

local notation "kpkg" => pkg_id.github_com.tangledbytes.go_vsr.examples.vsrnet

set_option goose.wp.extras true

theorem wp_digit (n : w64) :
    {{ (True : IProp GF) }}
      (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.digit)) (Val #n))
    {{ (s : GoString), RET #s; ⌜DigitsB s ∧ s.length = 1⌝ }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (uint.Z (W64 48 + n % W64 10))]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply wp_bytes_to_string $$ [Hsl] as -
  · iexact Hsl
  iapply HΦ
  ipureintro
  refine ⟨⟨by simp, by simp, ?_⟩, rfl⟩
  intro b hb
  simp only [List.mem_singleton] at hb
  subst hb
  exact digitB_of n

theorem wp_digits_aux (k : Nat) : ∀ n : w64, uint.nat n < 10 ^ (k + 1) →
    {{ (True : IProp GF) }}
      (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.digits)) (Val #n))
    {{ (s : GoString), RET #s; ⌜s ≠ [] ∧ s.length ≤ k + 1 ∧ ∀ b ∈ s, DigitB b⌝ }} := by
  induction k with
  | zero =>
    intro n hn
    wp_start as -
    wp_auto
    wp_if_destruct
    · wp_apply wp_digit as %s %Hs
      iapply HΦ
      ipureintro
      exact ⟨Hs.1.1, by omega, Hs.1.2.2⟩
    · exfalso; simp at hn; word
  | succ k ih =>
    intro n hn
    wp_start as -
    wp_auto
    wp_if_destruct
    · wp_apply wp_digit as %s %Hs
      iapply HΦ
      ipureintro
      exact ⟨Hs.1.1, by omega, Hs.1.2.2⟩
    · wp_apply ih (n / W64 10) (by rw [Nat.pow_succ] at hn; word) as %s1 %Hs1
      wp_apply wp_digit as %s2 %Hs2
      iapply HΦ
      ipureintro
      refine ⟨by simp [Hs1.1], by simp; omega, ?_⟩
      intro b hb
      rcases List.mem_append.1 hb with h | h
      · exact Hs1.2.2 b h
      · exact Hs2.1.2.2 b h

theorem wp_digits (n : w64) :
    {{ (True : IProp GF) }}
      (App (Val (@! github_com.tangledbytes.go_vsr.examples.vsrnet.digits)) (Val #n))
    {{ (s : GoString), RET #s; ⌜DigitsB s⌝ }} := by
  iintro %Φ - HΦ
  iapply wp_digits_aux 19 n (by word) $$ []
  · itrivial
  iintro !> %s %Hs
  iapply HΦ
  ipureintro
  exact ⟨Hs.1, Hs.2.1, Hs.2.2⟩

/-- `Gen`: client `c`'s input, one the kit accepts. -/
abbrev Gen.spec : Prop :=
  ⊢ EtcdGrove.lintest.genSpec (GF := GF)
      (functions github_com.tangledbytes.go_vsr.examples.vsrnet.Gen [])
      (fun x => iprop(∃ i : KIn, ⌜x = inV i.1⌝))

theorem Gen.wp_proof : Gen.spec (GF := GF) (hG := hG) := by
  unfold Gen.spec EtcdGrove.lintest.genSpec
  iintro %id
  wp_start as _
  wp_auto
  wp_apply github_com.goose_lang.primitive.RandomUint64.wp_proof as %r -
  wp_apply wp_digit as %d %Hd
  wp_if_destruct
  · wp_apply wp_digit as %d2 %Hd2
    wp_apply wp_digits as %ds %Hds
    iapply HΦ
    imodintro
    ipureintro
    exact ⟨⟨_, kin_put d d2 ds Hd Hd2 Hds⟩, rfl⟩
  · iapply HΦ
    imodintro
    ipureintro
    exact ⟨⟨_, kin_get d Hd⟩, rfl⟩

end proof

end github_com.tangledbytes.go_vsr.examples.vsrnet
end Perennial

/-
A slice of `w64`s owned in memory has fewer than `2^44` elements: its bytes lie below
`maxAddr = 2^47`. U2 uses it for `sort.Sort`'s bound (`xs.length ≤ 2^62`). A general fact about
Perennial's definitions, kept here as a local lemma (`notes/perennial-changes.md` candidate).
-/
module

public import Perennial.Golang.Theory.Unsafe
public import Perennial.Golang.Theory.Plain
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode

section
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The bytes of a non-empty byte points-to lie in `(0, maxAddr]`. -/
theorem bytesPointsto_in_bounds' (l : Loc) (dq : DFrac) (bs : List w8) (h : bs ≠ []) :
    bytesPointsto (GF := GF) l dq bs ⊢ ⌜0 < l.addr ∧ l.addr + bs.length ≤ maxAddr⌝ := by
  induction bs generalizing l with
  | nil => exact absurd rfl h
  | cons b bs ih =>
    unfold bytesPointsto
    iintro ⟨Hb, Hbs⟩
    icases heapPointsto_pos l dq _ $$ Hb with %H1
    icases heapPointsto_lt_maxAddr l dq _ $$ Hb with %H2
    cases bs with
    | nil => ipureintro; simp; omega
    | cons b' bs' =>
      icases ih (l +ₗ 1) (by simp) $$ Hbs with %H3
      ipureintro
      simp only [Loc.add, List.length_cons] at H3 ⊢
      omega

/-- An owned slice of `w64`s has fewer than `2^44` elements. -/
theorem ownSlice_w64_len (s : GoSlice) (vs : List w64) (dq : DFrac) :
    (s ↦*{dq} vs : IProp GF) ⊢ s ↦*{dq} vs ∗ ⌜vs.length < 2 ^ 44⌝ := by
  cases hvs : vs with
  | nil => iintro H; iframe H; ipureintro; simp
  | cons v vs' =>
    rw [← hvs]
    iintro H
    icases ownSlice_ptr_pos s vs dq (by simp [hvs]) $$ H with %Hpos
    icases ownSlice_bytes_acc go.uint64 (.scalar _ _ .isPlainScalar_uint64) s vs dq Hpos $$ H
      with ⟨Hb, Hback⟩
    have hlen : (vs.flatMap (encode (V := w64))).length = 8 * vs.length := by
      rw [List.length_flatMap]
      simp only [ByteEncoding.encode_length, List.map_const', List.sum_replicate_nat]
      omega
    icases bytesPointsto_in_bounds' s.ptr dq _ (by
      intro h; have := congrArg List.length h; rw [hlen, hvs] at this; simp at this) $$ Hb
      with %Hbnd
    isplitl
    · iapply Hback $$ %vs [] Hb
      ipureintro; rfl
    · ipureintro
      rw [hlen] at Hbnd
      unfold maxAddr at Hbnd
      omega

end

end bbolt
end EtcdGrove
end Perennial

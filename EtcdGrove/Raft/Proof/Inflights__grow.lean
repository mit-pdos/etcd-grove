/-
Port of election_proof/proof_Inflights__grow.v.
-/
import EtcdGrove.Raft.Spec.Inflights__grow

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
theorem tracker.Inflights.grow.wp_proof : tracker.Inflights.grow.spec (GF := GF) (hG := hG) := by
  intro l r Hsmall
  wp_start as H
  iNamed H
  iunfold ownInflightsRaw at Hin
  iNamed Hin
  subst Hring
  -- `len(in.buffer)` is the `slice.len` field; the pure length of `buf` is what both
  -- the premise and the postcondition speak about.
  ihave %Hblen := ownSlice_len $$ Hbuf
  wp_auto
  have Hok := Hinfl_ok
  unfold InflightsOk at Hok
  simp only [inflightsRingOf, inflightsAbs] at Hok Hsmall ⊢
  have Hsize : sint.Z iv.size' < 2 ^ 62 := Hok.2.2.2.1
  -- The three branches of the `newSize` computation differ only in the literal that
  -- reaches `make`; everything after it is joined.
  have Hlen0 : (buf.length : Int) = sint.Z iv.buffer'.len := by
    rw [Hblen.1]; unfold sint.nat; exact Int.toNat_of_nonneg Hblen.2
  wp_join iprop(∃ (n : w64), newSize_ptr ↦ n ∗ l ↦ iv ∗ in_ptr ↦ l ∗
      ⌜sint.Z n = max 1 (min (2 * (buf.length : Int)) (sint.Z iv.size'))⌝)
    with [newSize Hiv «in»] as ⟨%n, newSize, Hiv, «in», %Hn⟩
  · -- `len(buffer) * 2 == 0`. The product cannot wrap -- `len(buffer)` is below
    -- `size < 2^62` -- so this says the buffer is empty, and the new size is the
    -- literal 1. `size ≥ 1` by `Hsmall`, so `1 ≤ size`.
    iexists _; iframe newSize Hiv «in»
    ipureintro
    word
  · wp_if_destruct
    · -- `2 * len(buffer) > size`: cap at `size`.
      isplitr; · ipureintro; trivial
      iexists _; iframe newSize Hiv «in»
      ipureintro
      word
    · -- `2 * len(buffer) ≤ size`: double.
      isplitr; · ipureintro; trivial
      iexists _; iframe newSize Hiv «in»
      ipureintro
      word
  -- `wp_slice_make2` steps the store of the fresh slice into `newBuffer`, and
  -- `wp_slice_copy` leaves the destination at `take (len dst) src ++ drop (len src) dst`;
  -- with `dst` a `replicate` and `len src ≤ len dst` that is `buf ++ replicate (new - old)
  -- zero`.
  wp_apply wp_slice_make2 (V := tracker.inflight) n as %sl ⟨Hsl, Hsl_cap⟩
  · ipureintro; omega
  wp_apply wp_slice_copy (V := tracker.inflight) $$ [$Hsl $Hbuf] as %ncopy ⟨%Hncopy, Hsl, Hbuf⟩
  have Hsn : sint.nat n = (sint.Z n).toNat := rfl
  have Hle : buf.length ≤ sint.nat n := by rw [Hsn]; omega
  rw [List.length_replicate, List.take_of_length_le Hle, List.drop_replicate]
  iapply HΦ
  unfold ownInflightsRaw
  iexists { iv with buffer' := sl }, _
  simp only [named]
  iframe Hiv Hsl Hsl_cap
  ipureintro
  -- the state the new value and buffer denote is the old one at the new length; the
  -- ring invariant at the grown buffer: every field but `buffer` is unchanged, and
  -- the occupied range still fits because the buffer only got longer. `len buf < size`
  -- rules out the "buffer is the full ring" disjunct of the old invariant.
  have Hlenn : ((sint.nat n : Nat) : Int) = sint.Z n := by rw [Hsn]; omega
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := Hok
  simp only [inflightsRingOf, inflightsAbs, InflightsOk, List.length_append,
    List.length_replicate, InflightsRing.mk.injEq, true_and]
  rw [Nat.add_sub_cancel' Hle, Hlenn]
  refine ⟨Hn.symm, h1, h2, ⟨by omega, by omega⟩, h4, h5, Or.inl ?_⟩
  rcases h6 with h6 | h6 <;> omega

end proof

end EtcdGrove
end Perennial

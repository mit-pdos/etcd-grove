/-
Port of election_proof/proof_Inflights__Add.v.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.Inflights__Add
public import Spec.go_etcd_io.raft.v3.tracker.Inflights__Full
public import Spec.go_etcd_io.raft.v3.tracker.Inflights__grow

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit ext ffi [FfiInterp ffi] [FfiSemantics ext ffi] [GoGlobalContext] in
private theorem ite_of_true {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

set_option hygiene false in
/-- The tail shared by the three reachable leaves: write the new
`inflight` into slot `next` of whatever buffer `Hbuf` now holds, bump
`count` and `bytes`, and hand back `ownInflights`. (Rocq `Ltac add_store`; the stored value is
always `⟨index, bytes⟩`, so it is not a parameter here.) -/
macro "inflights_add_store" : tactic => `(tactic| (
  try wp_auto
  rw [ite_of_true (by word)]
  wp_auto
  wp_apply wp_store_slice_index (V := tracker.inflight) (t := tracker.inflight.ty) _ _ _
    ⟨index, bytes⟩ $$ [Hbuf] as Hbuf
  · iframe; ipureintro; word
  wp_auto
  iapply HΦ
  iapply ownInflights_reseal $$ Hiv Hbuf Hbuf_cap
  ipureintro
  constructor
  · simp only [InflightsOk, inflightsRingOf, inflightsAbs, List.length_set]
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;>
      first | word | (left; word) | (right; word)
  · simp only [inflightsAbs, inflightsAdd]
    congr 1 <;> word))

/-- `in.Add(index, bytes)`.

The premise `inflightsFull i = false` does two jobs. Directly it
rules out the opening `panic`. Indirectly it gives `count < size`,
hence `0 < size`, hence (by `InflightsOk`'s fifth conjunct)
`start < size` -- and those are what make the index arithmetic
bounded: `start + count < 2 * size < 2^63`, so the `go.int` addition
cannot overflow, and the wrapped `next` lands in `[0, size)`.

Three reachable leaves, by the two `if`s:

- `start + count ≥ size` (the ring wraps). Then
  `len(buffer) ≤ size ≤ start + count`, so the first disjunct of
  `InflightsOk`'s last conjunct is only satisfiable together with the
  second, i.e. `len(buffer) = size`: the buffer is already the whole
  ring. Hence `next < size = len(buffer)` and the `grow` arm is
  **dead** -- that is the `exfalso`. The invariant survives
  `count++` through `len(buffer) = size`.
- no wrap, `next < len(buffer)`. Here `next = start + count`, so
  `start + count + 1 ≤ len(buffer)`: the invariant survives through
  its *first* disjunct.
- no wrap, `next ≥ len(buffer)`: `grow`. `InflightsOk` gives
  `start + count ≤ len(buffer)` (the second disjunct would make
  `len(buffer) = size > next ≥ len(buffer)`), so with the test
  `next = start + count = len(buffer) < size` -- which is exactly
  `grow`'s premise. `grow` returns a buffer of
  `max 1 (min (2 * len(buffer)) size)` slots, strictly more than
  `len(buffer)`, so the write is in range and
  `start + count + 1 ≤ len(buffer')` again. -/
theorem tracker.Inflights.Add.wp_proof
    (wp_Inflights_Full : tracker.Inflights.Full.spec (GF := GF) (hG := hG))
    (wp_Inflights_grow : tracker.Inflights.grow.spec (GF := GF) (hG := hG)) :
    tracker.Inflights.Add.spec (GF := GF) (hG := hG) := by
  intro l i index bytes Hfull
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_Inflights_Full $$ [$Hin] as Hin
  rw [Hfull]
  iNamed Hin
  iNamed Hin
  subst Hring
  subst Hiabs
  have Hok := Hinfl_ok
  simp only [inflightsRingOf] at Hfull ⊢
  simp only [InflightsOk, inflightsRingOf, inflightsAbs] at Hinfl_ok
  rw [inflightsFull_abs] at Hfull
  ihave %Hblen := ownSlice_len _ _ _ $$ Hbuf
  -- not full ⇒ `count ≠ size`, and with `InflightsOk` that is
  -- `count < size`, `0 < size` and `start < size`.
  simp only [Bool.or_eq_false_iff] at Hfull
  obtain ⟨Hcnt, -⟩ := Hfull
  have Hcnt' : iv.count' ≠ iv.size' := of_decide_eq_false Hcnt
  obtain ⟨Hs0, Hc, Hbl, Hsz, Hstart, Hring⟩ := Hinfl_ok
  have Hclt : sint.Z iv.count' < sint.Z iv.size' := by
    have : sint.Z iv.count' ≠ sint.Z iv.size' := fun h => Hcnt' (BitVec.toInt_inj.1 h)
    omega
  have Hszpos : 0 < sint.Z iv.size' := by omega
  have Hslt : sint.Z iv.start' < sint.Z iv.size' := by rcases Hstart with h | h <;> omega
  wp_auto
  wp_if_destruct
  · -- `start + count ≥ size`: the ring wraps, so the buffer is already
    -- the full ring.
    have HL : (buf.length : Int) = sint.Z iv.size' := by rcases Hring with h | h <;> word
    wp_if_destruct
    · -- unreachable: `next < size = len(buffer)`
      exfalso; word
    · inflights_add_store
  · -- no wrap: `next = start + count`
    wp_if_destruct
    · -- the occupied range reaches the end of the buffer: grow
      ihave Hin : ownInflightsRaw l (inflightsRingOf iv buf) $$ [Hiv Hbuf Hbuf_cap]
      · iapply ownInflightsRaw_intro $$ Hiv Hbuf Hbuf_cap
        ipureintro; exact Hok
      wp_apply wp_Inflights_grow l (inflightsRingOf iv buf)
          (by simp only [inflightsRingOf, inflightsAbs]; word)
        $$ [$Hin] as Hin
      -- re-open at the grown state: a new value that differs from `iv` only in its
      -- buffer, which is `buf'`, of the length `grow` says
      iunfold ownInflightsRaw at Hin
      icases Hin with ⟨%iv', %buf', Hiv, Hbuf, Hbuf_cap, %Hring', -⟩
      obtain ⟨st', c', b', sz', mb', sl⟩ := iv'
      simp only [inflightsRingOf, inflightsAbs, InflightsRing.mk.injEq, Inflights.mk.injEq]
        at Hring'
      obtain ⟨⟨Hc', Hsz', Hb', Hmb'⟩, Hst', Hlen⟩ := Hring'
      obtain rfl : st' = iv.start' := by word
      obtain rfl : c' = iv.count' := by word
      obtain rfl : b' = iv.bytes' := by word
      obtain rfl : sz' = iv.size' := by word
      obtain rfl : mb' = iv.maxBytes' := by word
      ihave %Hblen' := ownSlice_len _ _ _ $$ Hbuf
      inflights_add_store
    · inflights_add_store

end proof

end EtcdGrove
end Perennial

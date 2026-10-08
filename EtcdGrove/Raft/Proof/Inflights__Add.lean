/-
Port of election_proof/proof_Inflights__Add.v.
-/
import EtcdGrove.Raft.Spec.Inflights__Add
import EtcdGrove.Raft.Spec.Inflights__Full
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

omit ext ffi [FfiInterp ffi] [FfiSemantics ext ffi] [GoGlobalContext] in
private theorem ite_of_true {α : Sort _} {c : Prop} [Decidable c] (h : c) (a b : α) :
    (if c then a else b) = a := by simp [h]

set_option hygiene false in
/-- The tail shared by the three reachable leaves: write the new
`inflight` into slot `next` of whatever buffer `Hbuf` now holds, bump
`count` and `bytes`, and hand back `ownInflights`. (Rocq `Ltac add_store`; the stored value is
always `⟨index, bytes⟩`, so it is not a parameter here.) -/
macro "inflights_add_store" : tactic => `(tactic| (
  rw [ite_of_true (by word)]
  wp_pures
  wp_apply wp_store_slice_index (V := tracker.inflight) (t := tracker.inflight.ty) _ _ _
    ⟨index, bytes⟩ $$ [Hbuf] as Hbuf
  · iframe; ipureintro; word
  wp_pures
  -- `in.count++`, `in.bytes += bytes`
  wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_store; wp_pures
  wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_store; wp_pures
  iapply HΦ
  iexists _, _
  simp only [named]
  iframe
  ipureintro
  constructor
  · unfold InflightsOk
    simp only [List.length_set]
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
  wp_alloc in_ptr as «in»; wp_pures; wp_alloc bytes_ptr as bytes; wp_pures
  wp_alloc index_ptr as index; wp_pures; wp_load; wp_pures
  wp_apply wp_Inflights_Full $$ [$Hin] as Hin
  rw [Hfull]
  unfold ownInflights
  iNamed Hin
  unfold ownInflightsRaw
  iNamed Hin
  subst Hiabs
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
  wp_pures; wp_load; wp_pures; wp_load; wp_load; wp_pures; wp_load; wp_pures
  wp_alloc next_ptr as next; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load; wp_pures
  wp_alloc size_ptr as size; wp_pures; wp_store; wp_pures; wp_load; wp_load; wp_pures
  wp_if_destruct
  · wp_load; wp_load; wp_pures; wp_store; wp_pures; wp_load; wp_load; wp_pures; wp_load; wp_pures
    iclear size
    -- `start + count ≥ size`: the ring wraps, so the buffer is already
    -- the full ring.
    have HL : (buf.length : Int) = sint.Z iv.size' := by rcases Hring with h | h <;> word
    wp_if_destruct
    · wp_load; wp_pures
      -- unreachable: `next < size = len(buffer)`
      exfalso; word
    · wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_load; wp_pures
      iclear index next
      inflights_add_store
  · wp_load; wp_load; wp_pures; wp_load; wp_pures; iclear size
    -- no wrap: `next = start + count`
    wp_if_destruct
    · wp_load; wp_pures
      -- the occupied range reaches the end of the buffer: grow
      ihave Hin : ownInflightsRaw l iv buf $$ [Hiv Hbuf Hbuf_cap]
      · unfold ownInflightsRaw
        simp only [named]
        iframe
        ipureintro
        exact ⟨Hs0, Hc, Hbl, Hsz, Hstart, Hring⟩
      wp_apply wp_Inflights_grow _ _ _ (by word) (by word) $$ [$Hin] as %sl %buf' Hg
      wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear index
      iNamed Hg
      unfold ownInflightsRaw
      iNamed Hin
      -- `ownInflightsRaw` states the buffer as `{ iv with buffer' := sl }.buffer'`;
      -- `inflights_add_store`'s `word` needs it as `sl`
      dsimp only at Hinfl_ok ⊢
      ihave %Hblen' := ownSlice_len _ _ _ $$ Hbuf
      wp_load; wp_load; wp_pures; iclear next
      inflights_add_store
    · wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_load; wp_pures
      iclear index next
      inflights_add_store

end proof

end EtcdGrove
end Perennial

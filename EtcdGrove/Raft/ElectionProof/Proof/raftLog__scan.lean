/-
Port of election_proof/proof_raftLog__scan.v.
-/
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__scan
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__slice

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

/-- `scan` is

      for lo < hi {
        ents, err := l.slice(lo, hi, pageSize)
        if err != nil { return err }
        if len(ents) == 0 { return fmt.Errorf("got 0 entries in [%d, %d)") }
        if err := v(ents); err != nil { return err }
        lo += uint64(len(ents))
      }
      return nil

Note what `slice` is called with: the *whole* remaining range
`[lo, hi)` with `pageSize` as its `maxSize`, not `min(hi, lo+pageSize)`
-- the page is cut by byte budget inside `slice`, and the only thing
`scan` knows about it is what `raftLog.slice.spec` states.

Three things carry the proof.

- The loop invariant is just the moving `lo`: `prev.index + 1 <= lo <=
  hi`, with `ownRaftLog` and the caller's `I` alongside. Only
  `lo` is written, so `hi`, `pageSize`, `l` and `v` stay in the frame
  `wp_for` sweeps up. No termination measure is needed: `wp_for` is
  Löb induction under a partial-correctness `WP`.
- Both error returns are dead. `slice`'s spec returns
  `#interface.nil` for the error, so the first `if` is skipped by
  `wp_auto` alone; the second needs `es ≠ []` from that spec, which
  via `ownSlice_len` gives `s.len ≠ 0`. The callback error is dead by
  construction: `scanClosure` demands `#interface.nil`.
- The callback gets the page with `∀ e ∈ es, P e`, which follows from the
  premise `∀ e ∈ sents ++ uents, P e` and the spec's "every entry of the page is an
  entry of the log".

The bound `lo + len(ents) <= hi` -- needed both to re-establish the
invariant and to show the `w64` addition does not wrap -- is exactly
`slice`'s `length es <= hi - lo`. `ownRaftLog`'s `Hnowrap` is not
needed and the predicate stays sealed throughout. -/
theorem raftLog.scan.wp_proof
    (wp_raftLog_slice : raftLog.slice.spec (GF := GF) (hG := hG)) :
    raftLog.scan.spec (GF := GF) (hG := hG) := by
  intro l ls lo hi pageSize f I P Hrange HP
  wp_start as H
  iNamed H
  wp_auto
  ihave IH : iprop(∃ (cur : w64),
      "lo" ∷ lo_ptr ↦ cur ∗
      "Hlog" ∷ ownRaftLog l ls ∗
      "HI" ∷ I ∗
      "%Hcur" ∷ ⌜uint.Z ls.prev.index' + 1 ≤ uint.Z cur ∧ uint.Z cur ≤ uint.Z hi⌝)
    $$ [lo Hlog HI]
  · iexists _
    iframe
    ipureintro; omega
  wp_for IH
  wp_if_destruct
  · -- one more page: `cur < hi`, so `slice`'s range premise holds
    have Hsl : uint.Z ls.prev.index' + 1 ≤ uint.Z cur ∧ uint.Z cur < uint.Z hi ∧
        uint.Z hi ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
          + (ls.uents.length : Int) + 1 := by omega
    wp_apply wp_raftLog_slice l ls cur hi pageSize Hsl $$ [$Hlog]
      as %s %es ⟨Hlog, #Hes, ⟨%Hne, %Hlen, %Hin, %_⟩, -⟩
    -- the "got 0 entries" error is dead: the page is non-empty
    ihave %Hslen := ownSlice_len $$ Hes
    have Hlen0 : es.length ≠ 0 := fun h => Hne (List.eq_nil_of_length_eq_zero h)
    have Hsne : s.len ≠ W64 0 := by
      intro Heq0; rw [Heq0] at Hslen; apply Hlen0; rw [Hslen.1]; rfl
    simp only [Hsne, decide_false]
    wp_auto
    -- every entry of the page is an entry of the log, so `P` holds
    have HPes : ∀ e ∈ es, P e := fun e he => HP e (Hin e he)
    iunfold scanClosure at Hf
    wp_apply Hf $$ %s %es %DFrac.discard [$Hes $HI] as ⟨-, HI⟩
    · ipureintro; exact HPes
    wp_for_post
    iframe
    iexists _
    iframe
    ipureintro
    constructor <;> word
  · iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial

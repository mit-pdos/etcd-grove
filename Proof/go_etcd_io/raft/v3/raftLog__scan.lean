/-
Port of election_proof/proof_raftLog__scan.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raftLog__scan
public import Spec.go_etcd_io.raft.v3.raftLog__slice

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

- The loop invariant is the moving `lo` (`cur`): `prev.index + 1 <= cur <= hi`, with
  `ownRaftLog` and the caller's state at the pages so far, `I (scanRange ls lo cur)`.
  Only `lo` is written, so `hi`, `pageSize`, `l` and `v` stay in the frame `wp_for`
  sweeps up. No termination measure is needed: `wp_for` is Löb induction under a
  partial-correctness `WP`.
- The `slice` error is dead (`slice`'s spec returns `#interface.nil`); the "got 0
  entries" error needs `es ≠ []` from that spec, which via `ownSlice_len` gives
  `s.len ≠ 0`. A callback error is returned as is, with the callback's `B err`.
- The page continues the pages so far: `slice` returns a prefix of the log from `cur`,
  which is the scanned range from `lo` with its first `cur - lo` entries dropped
  (`scanRange_page`).

The bound `lo + len(ents) <= hi` -- needed both to re-establish the
invariant and to show the `w64` addition does not wrap -- is exactly
`slice`'s `length es <= hi - lo`. `ownRaftLog`'s `Hnowrap` is not
needed and the predicate stays sealed throughout. -/
private theorem scanRange_page (ls : LogState) (lo cur hi n : w64) (es : List raftpb.Entry)
    (Hn : uint.Z n = (es.length : Int)) (Hlo : uint.Z ls.prev.index' + 1 ≤ uint.Z lo) (Hcur : uint.Z lo ≤ uint.Z cur)
    (Hhi : uint.Z cur + (es.length : Int) ≤ uint.Z hi)
    (Hend : uint.Z hi ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int) + 1)
    (Hpre : es <+: plogFrom ls.prev (ls.sents ++ ls.uents) cur) :
    scanRange ls lo cur ++ es <+: scanRange ls lo hi ∧
    scanRange ls lo cur ++ es = scanRange ls lo (cur + n) := by
  unfold scanRange plogFrom at *
  generalize HL : ls.sents ++ ls.uents = L at *
  have HLlen : (L.length : Int) = (ls.sents.length : Int) + (ls.uents.length : Int) := by
    rw [← HL, List.length_append]; push_cast; omega
  have Hdrop : L.drop (uint.Z cur - uint.Z ls.prev.index' - 1).toNat =
      (L.drop (uint.Z lo - uint.Z ls.prev.index' - 1).toNat).drop
        (uint.Z cur - uint.Z lo).toNat := by
    rw [List.drop_drop]; congr 1; omega
  rw [Hdrop] at Hpre
  generalize HM : L.drop (uint.Z lo - uint.Z ls.prev.index' - 1).toNat = M at *
  have HMlen : (M.length : Int) = (L.length : Int) - (uint.Z lo - uint.Z ls.prev.index' - 1) := by
    rw [← HM, List.length_drop]; omega
  have Hplen := Hpre.length_le
  rw [List.length_drop] at Hplen
  have Hnw : uint.Z (cur + n) = uint.Z cur + (es.length : Int) := by
    have := uint_Z_nonneg ls.prev.index'
    word
  obtain ⟨t, Ht⟩ := Hpre
  have Heq : M.take (uint.Z cur - uint.Z lo).toNat ++ es =
      M.take ((uint.Z cur - uint.Z lo).toNat + es.length) := by
    generalize Ha : (uint.Z cur - uint.Z lo).toNat = a at *
    have hM : M = M.take a ++ (es ++ t) := by rw [Ht, List.take_append_drop]
    have hlen : (M.take a).length = a := by rw [List.length_take]; omega
    have h2 := congrArg (List.take (a + es.length)) hM
    rw [h2]
    have key : ∀ (A X : List raftpb.Entry),
        (A ++ (es ++ X)).take (A.length + es.length) = A ++ es := by
      intro A X
      induction A with
      | nil => simp
      | cons x A ih => simp [Nat.succ_add, ih]
    calc M.take a ++ es
        = (M.take a ++ (es ++ t)).take ((M.take a).length + es.length) := (key _ _).symm
      _ = (M.take a ++ (es ++ t)).take (a + es.length) := by rw [hlen]
  refine ⟨?_, ?_⟩
  · rw [Heq]
    exact List.take_prefix_take_left (by omega)
  · rw [Heq, Hnw]; congr 1; omega

theorem raftLog.scan.wp_proof
    (wp_raftLog_slice : raftLog.slice.spec (GF := GF) (hG := hG)) :
    raftLog.scan.spec (GF := GF) (hG := hG) := by
  intro l ls lo hi pageSize f I B Hrange
  wp_start as H
  iNamed H
  wp_auto
  have H0 : scanRange ls lo lo = [] := by
    unfold scanRange; simp
  ihave IH : iprop(∃ (cur : w64),
      "lo" ∷ lo_ptr ↦ cur ∗
      "Hlog" ∷ ownRaftLog l ls ∗
      "HI" ∷ I (scanRange ls lo cur) ∗
      "%Hcur" ∷ ⌜uint.Z lo ≤ uint.Z cur ∧ uint.Z cur ≤ uint.Z hi⌝)
    $$ [lo Hlog HI]
  · iexists _
    rw [H0]
    iframe
    ipureintro; omega
  wp_for IH
  wp_if_destruct
  · -- one more page: `cur < hi`, so `slice`'s range premise holds
    have Hsl : uint.Z ls.prev.index' + 1 ≤ uint.Z cur ∧ uint.Z cur < uint.Z hi ∧
        uint.Z hi ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
          + (ls.uents.length : Int) + 1 := by omega
    wp_apply wp_raftLog_slice l ls cur hi pageSize Hsl $$ [$Hlog]
      as %s %es ⟨Hlog, #Hes, ⟨%Hne, %Hlen, %_, %Hpre⟩, -⟩
    -- the "got 0 entries" error is dead: the page is non-empty
    ihave %Hslen := ownSlice_len $$ Hes
    have Hlen0 : es.length ≠ 0 := fun h => Hne (List.eq_nil_of_length_eq_zero h)
    have Hsne : s.len ≠ W64 0 := by
      intro Heq0; rw [Heq0] at Hslen; apply Hlen0; rw [Hslen.1]; rfl
    simp only [Hsne, decide_false]
    wp_auto
    obtain ⟨Hsub, Hnext⟩ := scanRange_page ls lo cur hi s.len es (by word) Hrange.1 Hcur.1
      (by omega) Hrange.2.2 Hpre
    iunfold scanClosure at Hf
    wp_apply Hf $$ %s %(scanRange ls lo cur) %es %DFrac.discard [$Hes $HI] as %err ⟨-, Hres⟩
    · ipureintro; exact ⟨Hne, Hsub⟩
    icases Hres with (⟨%Herr, HI⟩ | ⟨%Herr, HB⟩)
    · subst Herr
      wp_auto
      wp_for_post
      iframe
      iexists _
      rw [Hnext]
      iframe
      ipureintro
      constructor <;> word
    · obtain ⟨i, rfl⟩ : ∃ i, err = GoInterface.ok i := by
        cases err with
        | nil => exact absurd rfl Herr
        | ok i => exact ⟨i, rfl⟩
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
      iright
      iframe
      ipureintro; exact Herr
  · iapply HΦ
    iframe
    ileft
    have Hc : cur = hi := by word
    subst Hc
    iframe
    ipureintro; rfl

end proof

end EtcdGrove
end Perennial

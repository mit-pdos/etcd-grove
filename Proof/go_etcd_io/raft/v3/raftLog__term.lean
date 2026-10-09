/-
Port of election_proof/proof_raftLog__term.v.

Lean notes: the Rocq `Local Lemma term_at_visible` is the private theorem
`termAt_visible`.
-/
module

public import Spec.go_etcd_io.raft.v3.raftLog__term
public import Spec.go_etcd_io.raft.v3.unstable__maybeTerm
public import Spec.go_etcd_io.raft.v3.raftLog__firstIndex
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex

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
omit [GoGlobalContext] in
/-- What `Storage.Term` answers (`termAt prev stored i`, `InvStorage.lean`) is
`plogTermAt` of the whole log on the visible stable range: the stored entries agree
with `sents` there, `sents` being a prefix. -/
private theorem termAt_visible (prev : entryID) (sents uents stored : List raftpb.Entry)
    (i t : w64) (Hpre : sents <+: stored)
    (Hr : uint.Z prev.index' ≤ uint.Z i ∧
      uint.Z i ≤ uint.Z prev.index' + (sents.length : Int))
    (Ht : termAt prev stored i = some t) :
    plogTermAt prev (sents ++ uents) i = some t := by
  obtain ⟨k, rfl⟩ := Hpre
  unfold termAt at Ht
  unfold plogTermAt
  rw [if_neg (by omega)]
  by_cases Heq : uint.Z i = uint.Z prev.index'
  · rw [if_pos Heq] at Ht ⊢; exact Ht
  · rw [if_neg Heq] at Ht ⊢
    rw [List.getElem?_append_left (by omega)] at Ht
    rw [List.getElem?_append_left (by omega)]
    exact Ht

/-- Four exits, in the order the body takes them (`raftLog.term.impl`,
`Code/go_etcd_io/raft/v3.lean`):

- `unstable.maybeTerm` said yes -- the index is in the unstable suffix, the term comes
  back with a `nil` error, and `ok`'s iff puts `i` in range;
- `i + 1 < l.firstIndex()` -- `(0, ErrCompacted)`. This is the one place `i + 1` can
  wrap: at `i = 2^64 - 1` the sum is `0`, which is below `firstIndex = prev.index + 1
  >= 1`, so the branch is taken. That is consistent with the iff because `Hnowrap` puts
  every in-range `i` at `<= 2^64 - 2`. The error is non-`nil` by `isInitialized`'s
  `HErrCompacted`;
- `i > l.lastIndex()` -- `(0, ErrUnavailable)`, likewise;
- otherwise `Storage.Term(i)`. Falling through both tests gives
  `prev.index <= i <= prev.index + |sents| + |uents|`, and `maybeTerm`'s `ok = false`
  rules out the unstable window, so `i <= prev.index + |sents|`: exactly `HTerm`'s
  premise. `HTerm` returns a `nil` error, so the `panic` below it is unreachable.

The two error returns read package-level globals, which is why `isInitialized_access`
appears at the top -- same reason as in `proof_raftLog__slice.v`, except that this body
only *returns* them and never compares against them, so the interface values need not
be case-split. Their non-`nil`-ness is what gives the `->` half of the postcondition's
iff on those two exits. -/
theorem raftLog.term.wp_proof
    (wp_unstable_maybeTerm : unstable.maybeTerm.spec (GF := GF) (hG := hG))
    (wp_raftLog_firstIndex : raftLog.firstIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG)) :
    raftLog.term.spec (GF := GF) (hG := hG) := by
  intro l ls i
  wp_start as H
  iNamed H
  ihave #Hinit := isInitialized_access $$ Hpkg
  iNamed Hinit
  iNamed Hlog
  wp_auto
  have Hnw : uint.Z lv.unstable'.offset' + (ls.uents.length : Int) < 2 ^ 64 := by omega
  -- a pending snapshot is `prev`, with nothing stable after it
  have Hsoff : ∀ sid, ls.snap = some sid →
      uint.Z lv.unstable'.offset' = uint.Z sid.index' + 1 := by
    intro sid Hs
    obtain ⟨rfl, Hse, -⟩ : LogStoreOk (some sid) σ ls.prev ls.sents ls.uents := Hs ▸ Hstore
    rw [Hse, List.length_nil, Int.natCast_zero, Int.add_zero] at Hoffset
    exact Hoffset
  ihave #Hsto : isStorageWith (ownStorage lv.storage') lv.storage' $$ [HisStorage]
  · unfold isStorage; iexact HisStorage
  unfold isStorageWith
  icases Hsto with ⟨%isv, #Hsto⟩
  iNamed Hsto
  lend_unstable
  wp_apply wp_unstable_maybeTerm _ (unstableOf lv ls) _ Hsoff Hnw $$ [$Hun]
    as %t %ok ⟨Hun, %Hok, %Hokt⟩
  reopen_unstable
  cases ok with
  | true =>
    -- the unstable suffix covers `i`, or `i` is the pending snapshot's
    wp_auto
    iapply HΦ $$ %t %interface.nil
    isplitl [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
    simp only [unstableOf, true_implies] at Hokt
    rcases Hokt with ⟨⟨Hlo, Hhi⟩, e, He, rfl⟩ | ⟨sid, Hs, rfl, rfl⟩
    · isplitr
      · ipureintro; exact ⟨fun _ => ⟨by omega, by omega⟩, fun _ => rfl⟩
      isplitr
      · ipureintro
        intro _
        apply plogTermAt_lookup _ _ _
          (ls.sents.length + (uint.Z i - uint.Z lv.unstable'.offset').toNat)
        · rw [List.getElem?_append_right (by omega)]
          rw [← He]
          congr 1
          omega
        · omega
      ileft; ipureintro; rfl
    · obtain ⟨Hsid, -, -⟩ : LogStoreOk (some sid) σ ls.prev ls.sents ls.uents := Hs ▸ Hstore
      subst Hsid
      isplitr
      · ipureintro; exact ⟨fun _ => ⟨by omega, by omega⟩, fun _ => rfl⟩
      isplitr
      · ipureintro; exact fun _ => plogTermAt_base _ _
      ileft; ipureintro; rfl
  | false =>
    have Hnotin : ¬ (uint.Z lv.unstable'.offset' ≤ uint.Z i ∧
        uint.Z i < uint.Z lv.unstable'.offset' + (ls.uents.length : Int)) := by
      intro Hc; exact absurd (Hok.2 (Or.inl Hc)) (by simp)
    have Hnotsnap : ∀ sid, ls.snap = some sid → i ≠ sid.index' := by
      intro sid Hs Hi; exact absurd (Hok.2 (Or.inr ⟨sid, Hs, Hi⟩)) (by simp)
    wp_auto
    ihave Hlog : ownRaftLog l ls $$ [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
    wp_apply wp_raftLog_firstIndex _ ls $$ [$Hlog] as %fi ⟨Hlog, %Hfi⟩
    by_cases Hb1 : uint.Z (i + W64 1) < uint.Z fi
    · -- below the compaction boundary: `ErrCompacted`
      rw [decide_eq_true Hb1]
      wp_auto
      iapply HΦ $$ %(W64 0) %errCompacted
      iframe Hlog
      isplitr
      · ipureintro
        exact ⟨fun Hc => absurd Hc HErrCompacted, fun _ => by exfalso; word⟩
      isplitr
      · ipureintro; intro Hc; exact absurd Hc HErrCompacted
      iright; ileft; iexact ErrCompacted
    rw [decide_eq_false Hb1]
    wp_auto
    wp_apply wp_raftLog_lastIndex _ ls $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
    by_cases Hb2 : uint.Z li < uint.Z i
    · -- past the last entry: `ErrUnavailable`
      rw [decide_eq_true Hb2]
      wp_auto
      iapply HΦ $$ %(W64 0) %errUnavailable
      iframe Hlog
      isplitr
      · ipureintro
        exact ⟨fun Hc => absurd Hc HErrUnavailable, fun _ => by exfalso; omega⟩
      isplitr
      · ipureintro; intro Hc; exact absurd Hc HErrUnavailable
      iright; iright; iexact ErrUnavailable
    -- in range, and not in the unstable window: ask the `Storage`
    rw [decide_eq_false Hb2]
    wp_auto
    have Hrange : uint.Z ls.prev.index' ≤ uint.Z i ∧
        uint.Z i ≤ uint.Z ls.prev.index' + (ls.sents.length : Int) := by
      constructor
      · word
      · omega
    -- with a snapshot pending the range is the snapshot's index alone, which
    -- `maybeTerm` answered
    cases Hs : ls.snap with
    | some sid =>
      exfalso
      obtain ⟨Hsid, Hse, -⟩ : LogStoreOk (some sid) σ ls.prev ls.sents ls.uents := Hs ▸ Hstore
      apply Hnotsnap sid Hs
      apply uint_Z_inj.1
      rw [Hse, List.length_nil, Int.natCast_zero, Int.add_zero, Hsid] at Hrange
      omega
    | none =>
    clear Hnotin Hnotsnap Hsoff Hnw Hok Hokt Hoffset Hstok Happlied Hpapplied Hcommitted
      Hidx Hnowrap HnoConfChange Hb1 Hb2 Hfi Hli Hcm Hap Hstore Hssnap
      Hapg Hip Hasz Hamx Hipb Hpersist Happlying Hpaused Huoff
    iclear HisStorage HLastIndex HFirstIndex HTerm HEntries Hbounded HSnapshot Hl_logger
      Hu_logger Husnap
    clear lv uv' isv fi li σ
    iNamed Hlog
    wp_auto
    ihave #Hsto : isStorageWith (ownStorage lv.storage') lv.storage' $$ [HisStorage]
    · unfold isStorage; iexact HisStorage
    unfold isStorageWith
    icases Hsto with ⟨%isv, #Hsto⟩
    iNamed Hsto
    rw [Hstok]
    obtain ⟨Hsp, Hstored, -⟩ : LogStoreOk none σ ls.prev ls.sents ls.uents := Hs ▸ Hstore
    have Hstlen := Hstored.length_le
    wp_apply HTerm $$ %σ %i [$HStorage] as %t2 ⟨%Ht2, HStorage⟩
    · ipureintro; rw [Hsp]; omega
    rw [Hsp] at Ht2
    rw [← Hstok]
    iapply HΦ $$ %t2 %interface.nil
    isplitl [Hl HStorage Huents Huents_cap]
    · reseal_raftLog
    isplitr
    · ipureintro; exact ⟨fun _ => ⟨Hrange.1, by omega⟩, fun _ => rfl⟩
    isplitr
    · ipureintro; exact fun _ => termAt_visible _ _ _ _ _ _ Hstored Hrange Ht2
    ileft; ipureintro; rfl

end proof

end EtcdGrove
end Perennial

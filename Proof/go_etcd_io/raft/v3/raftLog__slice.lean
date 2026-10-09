/-
Port of `election_proof/proof_raftLog__slice.v`.

Lean notes: Goose's `min` is stepped into (`wp_func_call; wp_call`) instead of
Rocq's `func_unfold`. The Rocq `Admitted` (`Hfitsx`, "the log fits in memory") was a
`sorry` here until 2026-10-08; `extend.spec` no longer needs the bound (see it).
-/
module

public import Spec.go_etcd_io.raft.v3.raftLog__slice
public import Spec.go_etcd_io.raft.v3.raftLog__mustCheckOutOfBounds
public import Spec.go_etcd_io.raft.v3.unstable__slice
public import Spec.go_etcd_io.raft.v3.limitSize
public import Spec.go_etcd_io.raft.v3.entsSize
public import Spec.go_etcd_io.raft.v3.extend

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

/-! Which entries `slice` returns, as list facts: each exit's result is a prefix of
the log from `lo` (`plogFrom`). -/
section prefix_helpers
omit ext ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx
variable {A : Type}

private theorem prefix_drop_take (a b : Nat) (l : List A) : (l.take b).drop a <+: l.drop a := by
  rw [List.drop_take]; exact List.take_prefix _ _
private theorem slice_stable_prefix (sents stored uents ese : List A) (k m : Nat)
    (Hs : sents <+: stored) (Hkm : k ≤ m) (Hm : m ≤ sents.length)
    (Hp : ese <+: (stored.take m).drop k) : ese <+: (sents ++ uents).drop k := by
  obtain ⟨r, rfl⟩ := Hs
  rw [List.take_append_of_le_length Hm] at Hp
  rw [List.drop_append_of_le_length (by omega)]
  exact (Hp.trans (prefix_drop_take _ _ _)).trans (List.prefix_append _ _)
private theorem slice_stable_full (sents stored ese : List A) (k : Nat)
    (Hs : sents <+: stored) (_Hk : k ≤ sents.length)
    (Hp : ese <+: (stored.take sents.length).drop k)
    (Hlen : sents.length - k ≤ ese.length) : ese = sents.drop k := by
  obtain ⟨r, rfl⟩ := Hs
  rw [List.take_left] at Hp
  exact Hp.eq_of_length (by have := Hp.length_le; simp at this ⊢; omega)
private theorem slice_unstable_prefix (s u : List A) (a b n : Nat) :
    ((u.take b).drop a).take n <+: (s ++ u).drop (s.length + a) := by
  rw [List.drop_append (l₁ := s), show s.drop (s.length + a) = [] from List.drop_eq_nil_of_le (by omega), List.nil_append,
    show s.length + a - s.length = a by omega]
  exact (List.take_prefix _ _).trans (prefix_drop_take _ _ _)
private theorem slice_both_prefix (s u : List A) (k b n : Nat) (Hk : k ≤ s.length) :
    s.drop k ++ ((u.take b).drop 0).take n <+: (s ++ u).drop k := by
  rw [List.drop_append_of_le_length Hk, List.drop_zero]
  exact (List.prefix_append_right_inj _).2 ((List.take_prefix _ _).trans (List.take_prefix _ _))

end prefix_helpers

/-- The body has three shapes of exit, and the range premise kills every error path on
the way:

- `lo >= unstable.offset`: the result is `limitSize(u.slice(lo, hi))`, re-sliced as
  `ents[0:len:len]`. `u.slice` hands out a read-only sub-slice, `limitSize` a prefix of
  that, and the three-index re-slice is the same pointer and length again -- so the
  read-only points-to travels through `ownSlice_same_ptr_len` (`InvRaftlog.lean`).
- `lo < unstable.offset` and `cut = min(hi, offset)`: `Storage.Entries` hands out the
  stable part, read-only. `cut` needs a case split (the builtin `min` is stepped into).
  Four of the exits return exactly that slice.
- the fifth exit is `extend(ents, unstable)`: a freshly allocated concatenation, made
  read-only before it is returned.

Nothing is lent, so every exit re-seals the log as it found it (`reseal_raftLog`).

Dead paths: `mustCheckOutOfBounds` returns `nil` (its own spec), `lo = hi` is excluded
by `lo < hi`, and `err = ErrCompacted` / `err = ErrUnavailable` are excluded because
`Storage.Entries` returns `interface.nil` and `isInitialized` (`Base.lean`, reached with
`isInitialized_access`) says both globals are non-nil. That is what makes the `Panicf`
and the bare `panic` unreachable.

**The former admission (`Hfitsx`, resolved 2026-10-08).** `extend` computes
`need := len(dst) + len(vals)` as a Go `int`, and its spec used to ask for
`|ents| + |unstable| < 2^63`. That bound is not derivable from the predicates:
`isStorage`'s `Hbounded` gives `prev.index + |sents| < 2^61`, `ownSlice_len` gives
`|uents| < 2^63`, and their sum clears `2^64` but not `2^63` -- the arithmetic
`InvRaftlog.lean`'s `Hnowrap` comment describes (tightening `Hnowrap` to `2^63` was
tried on 2026-09-20 and reverted: `raft.appendEntry` cannot re-establish a bound below
`2^63` across an `append`). So the Rocq script admits it (`Admitted. (* Trusted *)`,
"the log fits in memory"), and so did this file. The resolution is in `extend`'s spec:
past `2^63` the Go `int` wraps negative, the code takes its `append` branch, and the
`append` model assumes no length overflow -- the very assumption the admission stated
-- so `extend.spec` holds without the bound and nothing is admitted here. -/
theorem raftLog.slice.wp_proof
    (wp_raftLog_mustCheckOutOfBounds : raftLog.mustCheckOutOfBounds.spec (GF := GF) (hG := hG))
    (wp_unstable_slice : unstable.slice.spec (GF := GF) (hG := hG))
    (wp_limitSize : limitSize.spec (GF := GF) (hG := hG))
    (wp_entsSize : entsSize.spec (GF := GF) (hG := hG))
    (wp_extend : extend.spec (GF := GF) (hG := hG)) :
    raftLog.slice.spec (GF := GF) (hG := hG) := by
  intro l ls lo hi maxSize Hrange
  obtain ⟨Hr1, Hr2, Hr3⟩ := Hrange
  have Hmc : uint.Z ls.prev.index' + 1 ≤ uint.Z lo ∧ uint.Z lo ≤ uint.Z hi ∧
      uint.Z hi ≤ uint.Z ls.prev.index' + (ls.sents.length : Int) + (ls.uents.length : Int) + 1 :=
    ⟨Hr1, by omega, Hr3⟩
  wp_start as H
  iNamed H
  ihave #Hinit := isInitialized_access $$ Hpkg
  iNamed Hinit
  -- `err == ErrCompacted` and `err == ErrUnavailable` reduce to a `match` on the
  -- global's value, not to a `decide`, so the two globals have to be case-split;
  -- `isInitialized` says neither is `interface.nil`.
  cases errCompacted with
  | nil => exact absurd rfl HErrCompacted
  | ok ec =>
  cases errUnavailable with
  | nil => exact absurd rfl HErrUnavailable
  | ok eu =>
  wp_auto
  wp_apply wp_raftLog_mustCheckOutOfBounds l ls lo hi Hmc
    $$ [$Hlog] as Hlog
  rw [decide_eq_false (by rintro rfl; omega)]
  wp_auto
  iNamed Hlog
  ihave %Hulen := ownSlice_len $$ Huents
  wp_auto
  wp_if_destruct
  · -- the result lies entirely in the unstable suffix
    have Hus : uint.Z lv.unstable'.offset' ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
        uint.Z hi ≤ uint.Z lv.unstable'.offset' + (ls.uents.length : Int) := by omega
    have Hnwu : uint.Z lv.unstable'.offset' + (ls.uents.length : Int) < 2 ^ 64 := by omega
    lend_unstable
    wp_apply wp_unstable_slice _ (unstableOf lv ls) _ _ Hus Hnwu $$ [$Hun]
      as %s0 %es0 ⟨Hun, #Hs0, %Hes0p⟩
    obtain ⟨Hlen0, Hin0, Hcap0, Hes0⟩ := Hes0p
    wp_apply wp_limitSize $$ [$Hs0] as %s1 %nlim ⟨%Hn1, #Hs1, -⟩
    ihave %Hs1len := ownSlice_len $$ Hs1
    ihave %Hs1wf := ownSlice_wf $$ Hs1
    have Hne0 : es0 ≠ [] := by
      intro h; rw [h] at Hlen0; simp at Hlen0; omega
    have Hn1b := Hn1.2 Hne0
    have Hnetake : es0.take nlim ≠ [] := by
      intro h
      rw [List.take_eq_nil_iff] at h
      rcases h with h | h
      · omega
      · exact Hne0 h
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z s1.len ∧
      sint.Z s1.len ≤ sint.Z s1.len ∧ sint.Z s1.len ≤ sint.Z s1.cap by word)]
    wp_auto
    ihave Hs2 := ownSlice_same_ptr_len s1 (slice.fullSlice s1 raftpb.Entry (W64 0) s1.len s1.len)
      _ _ Hnetake (by simp only [slice.fullSlice, sliceIndexRef]
                      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0])
      (by simp only [slice.fullSlice]; word) (by simp only [slice.fullSlice]; word) $$ Hs1
    reopen_unstable
    ihave Hcap := ownSliceCap_empty (V := raftpb.Entry)
      (slice.fullSlice s1 raftpb.Entry (W64 0) s1.len s1.len) rfl
      (by simp only [slice.fullSlice]; word)
    iapply HΦ $$ %_ %(es0.take nlim)
    iframe Hs2 Hcap
    isplitl
    · reseal_raftLog
    ipureintro
    refine ⟨Hnetake, ?_, ?_, ?_⟩
    · rw [List.length_take]; omega
    · intro e He
      exact List.mem_append_right _ (Hin0 e (List.mem_of_mem_take He))
    · rw [Hes0]
      simp only [plogFrom, subslice]
      have Hk : (uint.Z lo - uint.Z ls.prev.index' - 1).toNat =
          ls.sents.length + (uint.Z lo - uint.Z lv.unstable'.offset').toNat := by omega
      rw [Hk]
      exact slice_unstable_prefix _ _ _ _ _
  · -- the result starts in the stable prefix: `lo < unstable.offset`. With a snapshot
    -- pending there is no stable prefix -- `offset` is `ls.prev.index + 1 <= lo` -- so this
    -- branch is dead, and `Storage` is never asked about the shadowed entries.
    rcases Option.eq_none_or_eq_some ls.snap with Hsn | ⟨sid, Hsn⟩
    rotate_left
    · exfalso
      obtain ⟨-, Hs, -⟩ : LogStoreOk (some sid) σ ls.prev ls.sents ls.uents := Hsn ▸ Hstore
      simp only [Hs, List.length_nil, Int.natCast_zero, Int.add_zero] at Hoffset
      omega
    obtain ⟨Hsp, Hstored, -⟩ : LogStoreOk none σ ls.prev ls.sents ls.uents := Hsn ▸ Hstore
    have Hstlen := Hstored.length_le
    ihave #Hsto : isStorageWith (ownStorage lv.storage') lv.storage' $$ [HisStorage]
    · unfold isStorage; iexact HisStorage
    unfold isStorageWith
    icases Hsto with ⟨%isv, #Hsto⟩
    iNamed Hsto
    icases Hbounded $$ HStorage with ⟨%Hsb, HStorage⟩
    wp_func_call
    wp_call
    -- every exit that returns the stable part `ese` alone
    have Hfin : ∀ (c : w64) (ese : List raftpb.Entry),
        uint.Z c ≤ uint.Z lv.unstable'.offset' → uint.Z c ≤ uint.Z hi →
        ese ≠ [] → (ese.length : Int) ≤ uint.Z c - uint.Z lo →
        (∀ e, e ∈ ese → e ∈ σ.ents.take (uint.Z c - uint.Z ls.prev.index' - 1).toNat) →
        ese <+: (σ.ents.take (uint.Z c - uint.Z ls.prev.index' - 1).toNat).drop
                  (uint.Z lo - uint.Z ls.prev.index' - 1).toNat →
        ese ≠ [] ∧ (ese.length : Int) ≤ uint.Z hi - uint.Z lo ∧
          (∀ e, e ∈ ese → e ∈ ls.sents ++ ls.uents) ∧
          ese <+: plogFrom ls.prev (ls.sents ++ ls.uents) lo := by
      intro c ese Hc1 Hc2 Hne Hlen Hin Hpre
      refine ⟨Hne, by omega, fun e He => List.mem_append_left _
        (stored_take_visible ls.prev ls.sents σ.ents c e Hstored (by omega) (Hin e He)), ?_⟩
      simp only [plogFrom]
      exact slice_stable_prefix ls.sents σ.ents ls.uents ese _ _ Hstored (by omega) (by omega) Hpre
    by_cases Hcut : uint.Z hi < uint.Z lv.unstable'.offset'
    · -- cut = hi: the whole range is in storage
      rw [decide_eq_true Hcut]
      wp_auto
      rw [Hstok]
      wp_apply HEntries $$ %σ %lo %hi %maxSize [$HStorage]
        as %se %ese ⟨#Hse, %Hpost, HStorage⟩
      · ipureintro; rw [Hsp]; omega
      rw [Hsp] at Hpost
      rw [← Hstok]
      obtain ⟨Hnee, Hlene, Hine, Hcape, Hpre⟩ := Hpost
      rw [decide_eq_true (by omega)]
      wp_auto
      ihave %Hselen := ownSlice_len $$ Hse
      ihave Hcap := ownSliceCap_empty (V := raftpb.Entry) se Hcape.symm (by omega)
      iapply HΦ $$ %se %ese
      iframe Hse Hcap
      isplitl
      · reseal_raftLog
      ipureintro
      exact Hfin hi ese (by omega) (by omega) Hnee Hlene Hine Hpre
      done
    · -- cut = unstable.offset
      rw [decide_eq_false Hcut]
      wp_auto
      rw [Hstok]
      wp_apply HEntries $$ %σ %lo %lv.unstable'.offset' %maxSize [$HStorage]
        as %se %ese ⟨#Hse, %Hpost, HStorage⟩
      · ipureintro; rw [Hsp]; omega
      rw [Hsp] at Hpost
      rw [← Hstok]
      obtain ⟨Hnee, Hlene, Hine, Hcape, Hpre⟩ := Hpost
      ihave %Hselen := ownSlice_len $$ Hse
      wp_if_destruct
      · -- `hi <= offset`, i.e. `hi = offset`: the result is exactly the stable part
        ihave Hcap := ownSliceCap_empty (V := raftpb.Entry) se Hcape.symm (by omega)
        iapply HΦ $$ %se %ese
        iframe Hse Hcap
        isplitl
        · reseal_raftLog
        ipureintro
        exact Hfin _ ese (by omega) (by omega) Hnee Hlene Hine Hpre
      wp_if_destruct
      · -- storage returned fewer entries than asked for: stop there
        ihave Hcap := ownSliceCap_empty (V := raftpb.Entry) se Hcape.symm (by omega)
        iapply HΦ $$ %se %ese
        iframe Hse Hcap
        isplitl
        · reseal_raftLog
        ipureintro
        exact Hfin _ ese (by omega) (by omega) Hnee Hlene Hine Hpre
      rename_i Hnotshort0
      wp_apply wp_entsSize $$ [$Hse] as %sz1 -
      wp_if_destruct
      · -- the stable part already reaches `maxSize`
        ihave Hcap := ownSliceCap_empty (V := raftpb.Entry) se Hcape.symm (by omega)
        iapply HΦ $$ %se %ese
        iframe Hse Hcap
        isplitl
        · reseal_raftLog
        ipureintro
        exact Hfin _ ese (by omega) (by omega) Hnee Hlene Hine Hpre
      have Hus : uint.Z lv.unstable'.offset' ≤ uint.Z lv.unstable'.offset' ∧
          uint.Z lv.unstable'.offset' < uint.Z hi ∧
          uint.Z hi ≤ uint.Z lv.unstable'.offset' + (ls.uents.length : Int) := by omega
      have Hnwu : uint.Z lv.unstable'.offset' + (ls.uents.length : Int) < 2 ^ 64 := by omega
      lend_unstable
      wp_apply wp_unstable_slice _ (unstableOf lv ls) _ _ Hus Hnwu $$ [$Hun]
        as %s0 %es0 ⟨Hun, #Hs0, %Hes0p⟩
      obtain ⟨Hlen0, Hin0, Hcap0, Hes0⟩ := Hes0p
      wp_apply wp_limitSize $$ [$Hs0] as %s1 %nlim ⟨%Hn1, #Hs1, -⟩
      reopen_unstable
      have Hne0 : es0 ≠ [] := by
        intro h; rw [h] at Hlen0; simp at Hlen0; omega
      have Hn1b := Hn1.2 Hne0
      have Hlentake : (es0.take nlim).length = nlim := by rw [List.length_take]; omega
      have Hintake : ∀ e, e ∈ es0.take nlim → e ∈ ls.uents :=
        fun e He => Hin0 e (List.mem_of_mem_take He)
      have Hcapx : sint.Z se.cap < (ese.length : Int) + ((es0.take nlim).length : Int) := by
        have : ((sint.nat se.len : Nat) : Int) = sint.Z se.len := by word
        rw [Hcape, Hselen.1]; omega
      -- `Storage.Entries` returned the whole range `[lo, offset)`: the
      -- `len(ents) < cut-lo` fast path was not taken
      have Hese : ese = ls.sents.drop (uint.Z lo - uint.Z ls.prev.index' - 1).toNat := by
        apply slice_stable_full ls.sents σ.ents ese _ Hstored (by omega)
        · rw [show ls.sents.length = (uint.Z lv.unstable'.offset' - uint.Z ls.prev.index' - 1).toNat
            by omega]
          exact Hpre
        · word
      have Hext : ese ++ es0.take nlim ≠ [] ∧
          ((ese ++ es0.take nlim).length : Int) ≤ uint.Z hi - uint.Z lo ∧
          (∀ e, e ∈ ese ++ es0.take nlim → e ∈ ls.sents ++ ls.uents) ∧
          ese ++ es0.take nlim <+: plogFrom ls.prev (ls.sents ++ ls.uents) lo := by
        refine ⟨by simp [Hnee], by rw [List.length_append]; omega, ?_, ?_⟩
        · intro e He
          rcases List.mem_append.1 He with He | He
          · exact List.mem_append_left _
              (stored_take_visible ls.prev ls.sents σ.ents _ e Hstored (by omega) (Hine e He))
          · exact List.mem_append_right _ (Hintake e He)
        · rw [Hese, Hes0]
          simp only [plogFrom, subslice, Int.sub_self, Int.toNat_zero]
          exact slice_both_prefix ls.sents ls.uents _ _ _ (by omega)
      wp_if_destruct
      · -- `len(unstable) == 1`: one more size check before giving up
        wp_apply wp_entsSize $$ [$Hs1] as %sz2 -
        wp_if_destruct
        · -- the single unstable entry does not fit
          ihave Hcap := ownSliceCap_empty (V := raftpb.Entry) se Hcape.symm (by omega)
          iapply HΦ $$ %se %ese
          iframe Hse Hcap
          isplitl
          · reseal_raftLog
          ipureintro
          exact Hfin _ ese (by omega) (by omega) Hnee Hlene Hine Hpre
        iapply wp_fupd
        wp_apply wp_extend _ _ _ _ _ _ Hcapx $$ [$Hse $Hs1] as %sx ⟨Hsx, Hsxcap, -, -⟩
        ipersist Hsx
        imodintro
        iapply HΦ $$ %sx %_
        iframe Hsx Hsxcap
        isplitl
        · reseal_raftLog
        ipureintro
        exact Hext
      · iapply wp_fupd
        wp_apply wp_extend _ _ _ _ _ _ Hcapx $$ [$Hse $Hs1] as %sx ⟨Hsx, Hsxcap, -, -⟩
        ipersist Hsx
        imodintro
        iapply HΦ $$ %sx %_
        iframe Hsx Hsxcap
        isplitl
        · reseal_raftLog
        ipureintro
        exact Hext

end proof

end EtcdGrove
end Perennial

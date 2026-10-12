/-
Port of `election_proof/proof_raftLog__append.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.raftLog__append
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.unstable__truncateAndAppend

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

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
/-- Rocq `truncate_append_split`: the new visible stable part and unstable suffix make
up `plogTruncateAppend` of the whole log. -/
private theorem truncateAppend_split (prev : entryID) (sents uents : List raftpb.Entry)
    (e0 : raftpb.Entry) (ents' : List raftpb.Entry) :
    sents.take (uint.Z e0.Index' - uint.Z prev.index' - 1).toNat ++
      (uents.take (uint.Z e0.Index' - uint.Z prev.index' - 1 - (sents.length : Int)).toNat
        ++ e0 :: ents') =
    plogTruncateAppend prev (sents ++ uents) (e0 :: ents') := by
  simp only [plogTruncateAppend, List.take_append, List.append_assoc]
  congr 3
  omega

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
private theorem truncateAppend_lengths (prev : entryID) (sents uents : List raftpb.Entry)
    (e0 : raftpb.Entry) (ents' : List raftpb.Entry)
    (H1 : uint.Z prev.index' < uint.Z e0.Index')
    (H2 : uint.Z e0.Index' ≤ uint.Z prev.index' + (sents.length : Int)
      + (uents.length : Int) + 1) :
    ((sents.take (uint.Z e0.Index' - uint.Z prev.index' - 1).toNat).length : Int) +
      ((uents.take (uint.Z e0.Index' - uint.Z prev.index' - 1 - (sents.length : Int)).toNat
        ++ e0 :: ents').length : Int) =
    uint.Z e0.Index' - uint.Z prev.index' - 1 + (ents'.length : Int) + 1 := by
  simp only [List.length_take, List.length_append, List.length_cons]
  omega

omit go_gctx in
/-- The persistence invariant across `truncateAndAppend` (the Rocq's `Hpers2`), stated
over the bare quantities: `E` the batch's first index, `P` the old `prev.index`, `kip`
and `k'` the old and new `offsetInProgress - offset`. -/
private theorem append_persistOk (σ : StorState)
    (lpend sents uents stored : List raftpb.Entry) (e0 : raftpb.Entry)
    (ents' : List raftpb.Entry) (E P kip k' : Int)
    (Hpre0 : (sents ++ uents.take kip.toNat) <+: storApp σ lpend)
    (Hst : storApp σ lpend = stored)
    (Hkip : kip.toNat ≤ uents.length)
    (HP : P < E) (HE : E ≤ P + (sents.length : Int) + (uents.length : Int) + 1)
    (Hk1 : k'.toNat ≤ kip.toNat)
    (Hk2 : E < P + (sents.length : Int) + (uents.length : Int) + 1 →
      k'.toNat ≤ (E - P - 1).toNat - sents.length)
    (Hk3 : E = P + (sents.length : Int) + (uents.length : Int) + 1 → k'.toNat = kip.toNat) :
    LogPersistOk σ (sents.take (E - P - 1).toNat)
      (uents.take (E - P - 1 - (sents.length : Int)).toNat ++ e0 :: ents') k' lpend stored := by
  refine ⟨?_, ?_, ?_, Hst⟩
  · refine List.IsPrefix.trans ?_ Hpre0
    rw [show (E - P - 1 - (sents.length : Int)).toNat = (E - P - 1).toNat - sents.length
      by omega]
    exact persist_prefix_truncate sents uents (e0 :: ents') _ _ _ Hkip (by omega)
      (fun _ => ⟨Hk1, Hk2 (by omega)⟩) (fun _ => Hk3 (by omega))
  · -- never all handed out: the batch is not
    intro Hfull
    exfalso
    simp only [List.length_append, List.length_take, List.length_cons] at Hfull
    by_cases Hlt : E < P + (sents.length : Int) + (uents.length : Int) + 1
    · have := Hk2 Hlt; omega
    · have := Hk3 (by omega); omega
  · intro Hnil; simp at Hnil

/-- Two exits. An empty batch returns `lastIndex()` with the log untouched. Otherwise
the `Panicf` is dead by the `committed` premise, `truncateAndAppend` gets the
`unstable` field (its offset is `prev.index + |sents| + 1`, `Hoffset`), and the log is
re-sealed at `logTruncateAppend`: same storage state `σ`, the visible stable part cut at
`e0.Index` when the batch starts inside it. -/
theorem raftLog.append.wp_proof
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_unstable_truncateAndAppend : unstable.truncateAndAppend.spec (GF := GF) (hG := hG)) :
    raftLog.append.spec (GF := GF) (hG := hG) := by
  intro l ls ents es dq Hpre Hnorm
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hes
  cases ents with
  | nil =>
    -- `len(ents) == 0`: the log is untouched and the result is the old last index.
    -- The predicate does not have to be opened at all.
    simp only [List.length_nil] at Hlen
    rw [decide_eq_true (by word)]
    wp_auto
    wp_apply wp_raftLog_lastIndex _ ls $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
    iapply HΦ $$ %li
    simp only [logTruncateAppend, logAdopts, plogTruncateAppend, Bool.false_eq_true,
      ite_false]
    iframe Hlog Hes
    ipureintro
    exact ⟨trivial, Hli⟩
  | cons e0 ents' =>
    -- the batch is non-empty: `ents[0]` exists
    have He0 : (e0 :: ents')[0]? = some e0 := rfl
    obtain ⟨Hrange, Hcontig, Hnwb⟩ := Hpre e0 He0
    simp only [List.length_cons] at Hlen
    rw [decide_eq_false (by word)]
    wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z es.len by word)]
    icases ownSlice_elem_acc (sint.Z (W64 0)) e0 es dq (e0 :: ents') (by decide) He0 $$ Hes
      with ⟨He0, Hesback⟩
    -- (a field load through a fractional struct points-to is not found by `wp_auto`:
    -- take the field out by hand, as `Proof/unstable__truncateAndAppend.lean` does)
    icases (AccessStrict.access_strict
        (A := (sliceIndexRef raftpb.Entry (sint.Z (W64 0)) es).[raftpb.Entry, go!"Index"] ↦{dq}
          e0.Index')
        (A' := (sliceIndexRef raftpb.Entry (sint.Z (W64 0)) es).[raftpb.Entry, go!"Index"] ↦{dq}
          e0.Index')
        (P := sliceIndexRef raftpb.Entry (sint.Z (W64 0)) es ↦{dq} e0)) $$ He0 with ⟨He0, Hclose⟩
    wp_auto
    ihave He0 := Hclose $$ He0
    ihave Hes := Hesback $$ He0
    rw [show ((e0 :: ents').set (sint.Z (W64 0)).toNat e0) = e0 :: ents' from rfl]
    -- the `Panicf`: `after = e0.Index - 1 >= committed`
    iNamed Hlog
    wp_auto
    rw [decide_eq_false (by rw [Hcm]; word)]
    wp_auto
    -- hand the `unstable` field to `truncateAndAppend`
    have Hle' : uint.Z e0.Index' ≤ uint.Z lv.unstable'.offset' + (ls.uents.length : Int) := by
      omega
    have Hnw' : uint.Z lv.unstable'.offset' + (ls.uents.length : Int) < 2 ^ 64 := by omega
    -- the two adopt conditions agree
    have Hadopt_eq : (logAdopts ls (e0 :: ents') = true) =
        (uint.Z e0.Index' ≤ uint.Z lv.unstable'.offset' ∧
          uint.Z e0.Index' ≠ uint.Z lv.unstable'.offset' + (ls.uents.length : Int)) := by
      simp only [logAdopts, decide_eq_true_eq, Hoffset]
      apply propext; omega
    simp only [Hadopt_eq]
    lend_unstable
    wp_apply wp_unstable_truncateAndAppend _ (unstableOf lv ls) _ _ _ _ He0 Hle' Hnw'
        $$ [$Hun $Hes Hadopt] as ⟨Hun, Hes⟩
    · iexact Hadopt
    iclear Husnap Hu_logger
    icases ownUnstable_reopen _ _ _ $$ Hlback Hun
      with ⟨%uv', Hl, Hents_cap, Hents, #Husnap, #Hu_logger, %Hoffm, %Hoip'⟩
    have Hoff' : uint.Z uv'.offset' = min (uint.Z e0.Index') (uint.Z lv.unstable'.offset') := by
      rw [Hoffm, w64Min_spec]
    -- the new state
    have Hm : (uint.Z e0.Index' - uint.Z (unstableOf lv ls).offset).toNat =
        (uint.Z e0.Index' - uint.Z ls.prev.index' - 1 - (ls.sents.length : Int)).toNat := by
      simp only
      omega
    rw [Hm]
    have Hsplit := truncateAppend_split ls.prev ls.sents ls.uents e0 ents'
    have Hprev : uint.Z ls.prev.index' < uint.Z e0.Index' := by
      have := Happlied.1; omega
    have Hlens' := truncateAppend_lengths ls.prev ls.sents ls.uents e0 ents' (by omega) (by omega)
    have Hidx' : LogIndicesOk ls.prev
        (ls.sents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1).toNat ++
          (ls.uents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1
              - (ls.sents.length : Int)).toNat ++ e0 :: ents')) := by
      rw [Hsplit]
      refine PlogWf_truncateAppend _ _ _ e0 Hidx He0 ⟨Hprev, ?_⟩ Hcontig
      simp only [plogLastIndexZ, List.length_append]; push_cast; omega
    have Hnc' : ∀ e ∈ ls.sents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1).toNat ++
          (ls.uents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1
              - (ls.sents.length : Int)).toNat ++ e0 :: ents'), e.Type' = EntryNormal := by
      intro e He
      simp only [List.mem_append] at He
      rcases He with He | He | He
      · exact HnoConfChange e (List.mem_append_left _ (List.mem_of_mem_take He))
      · exact HnoConfChange e (List.mem_append_right _ (List.mem_of_mem_take He))
      · exact Hnorm e He
    -- the storage relation: the visible stable part is cut, or -- with a snapshot
    -- pending -- stays empty
    have Hst2 : LogStoreOk ls.snap σ ls.prev
        (ls.sents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1).toNat)
        (ls.uents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1
            - (ls.sents.length : Int)).toNat ++ e0 :: ents') := by
      rcases Option.eq_none_or_eq_some ls.snap with Hsn | ⟨sid, Hsn⟩ <;>
        rw [Hsn] at Hstore ⊢
      · obtain ⟨Hp, Hstored, -⟩ := Hstore
        exact ⟨Hp, (List.take_prefix _ _).trans Hstored, fun h => by simp at h⟩
      · obtain ⟨Hp, Hs, Hsid⟩ := Hstore
        exact ⟨Hp, by rw [Hs]; simp, Hsid⟩
    -- the storage's snapshot is at or below `committed`, so below the batch: its term
    -- survives the truncation
    have Hss2 : ls.snap = none → StoredSnapOk σ ls.committed ls.prev
        (ls.sents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1).toNat ++
          (ls.uents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1
              - (ls.sents.length : Int)).toNat ++ e0 :: ents')) := by
      intro Hs
      rcases Hssnap Hs with H | ⟨Hsle, Hst⟩
      · exact .inl H
      · refine .inr ⟨Hsle, ?_⟩
        rw [Hsplit]
        exact plogTermAt_truncateAppend_below _ _ _ e0 _ _ He0 (by omega) Hst
    have Hls' : ((ls.sents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1).toNat).length
          : Int)
        = min (uint.Z e0.Index' - uint.Z ls.prev.index' - 1) (ls.sents.length : Int) := by
      rw [List.length_take]; omega
    have Hnw2 : uint.Z ls.prev.index'
        + ((ls.sents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1).toNat).length : Int)
        + ((ls.uents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1
              - (ls.sents.length : Int)).toNat ++ e0 :: ents').length : Int) + 1 < 2 ^ 64 := by
      simp only [List.length_cons] at Hnwb; push_cast at Hnwb; omega
    have Hoff2 : uint.Z uv'.offset' = uint.Z ls.prev.index'
        + ((ls.sents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1).toNat).length
            : Int) + 1 := by
      rw [Hoff', Hls', Hoffset]; omega
    have Hcm2 : uint.Z ls.committed ≤ uint.Z ls.prev.index'
        + ((ls.sents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1).toNat).length : Int)
        + ((ls.uents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1
              - (ls.sents.length : Int)).toNat ++ e0 :: ents').length : Int) := by
      omega
    -- `offsetInProgress` (2026-10-05): `truncateAndAppend`'s arm-wise value is
    -- `logTruncInprogress`, and the persistence invariant survives
    -- (`persist_prefix_truncate`)
    have Hip2 : uv'.offsetInProgress' = logTruncInprogress ls e0.Index' := by
      simp only [Hoip', truncOffsetInProgress, logTruncInprogress, w64Min]
      repeat' split
      all_goals first | rfl | (exfalso; omega) | (apply uint_Z_inj.1; omega)
    have Hk' : (uint.Z (logTruncInprogress ls e0.Index') - uint.Z uv'.offset').toNat
          ≤ (uint.Z ls.inprogress - uint.Z lv.unstable'.offset').toNat ∧
        (uint.Z e0.Index' < uint.Z ls.prev.index' + (ls.sents.length : Int)
            + (ls.uents.length : Int) + 1 →
          (uint.Z (logTruncInprogress ls e0.Index') - uint.Z uv'.offset').toNat
            ≤ (uint.Z e0.Index' - uint.Z ls.prev.index' - 1).toNat - ls.sents.length) ∧
        (uint.Z e0.Index' = uint.Z ls.prev.index' + (ls.sents.length : Int)
            + (ls.uents.length : Int) + 1 →
          (uint.Z (logTruncInprogress ls e0.Index') - uint.Z uv'.offset').toNat
            = (uint.Z ls.inprogress - uint.Z lv.unstable'.offset').toNat) := by
      unfold logTruncInprogress
      repeat' split
      all_goals omega
    have Hipb2 : uint.Z uv'.offset' ≤ uint.Z (logTruncInprogress ls e0.Index') ∧
        uint.Z (logTruncInprogress ls e0.Index') ≤ uint.Z uv'.offset'
          + ((ls.uents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1
              - (ls.sents.length : Int)).toNat ++ e0 :: ents').length : Int) := by
      unfold logTruncInprogress
      simp only [List.length_append, List.length_take, List.length_cons]
      repeat' split
      all_goals omega
    have Hpers2 : ls.snap = none →
        LogPersistOk σ
          (ls.sents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1).toNat)
          (ls.uents.take (uint.Z e0.Index' - uint.Z ls.prev.index' - 1
              - (ls.sents.length : Int)).toNat ++ e0 :: ents')
          (uint.Z (logTruncInprogress ls e0.Index') - uint.Z uv'.offset') ls.unpersisted
          ls.stored := by
      intro Hs
      obtain ⟨Hpre0, -, -, Hst0⟩ := Hpersist Hs
      obtain ⟨Hk1, Hk2, Hk3⟩ := Hk'
      exact append_persistOk σ ls.unpersisted ls.sents ls.uents ls.stored e0 ents' _ _ _ _ Hpre0
        Hst0
        (by omega) Hprev (by omega) Hk1 Hk2 Hk3
    -- the storage's pending batch is above the (shorter) stable part (2026-10-10)
    have Hpend2 : PendLogOk σ (logTruncateAppend ls (e0 :: ents')) := by
      refine ⟨Hpend.1, fun Hs e1 He1 => ?_⟩
      have := Hpend.2 Hs e1 He1
      simp only [logTruncateAppend, List.length_take] at this ⊢
      omega
    ihave Hlog : ownRaftLog l (logTruncateAppend ls (e0 :: ents'))
        $$ [Hl HStorage Hents Hents_cap]
    · iapply ownRaftLog_intro l { lv with unstable' := uv' } lv.storage' σ _ _
          (logTruncateAppend ls (e0 :: ents')) rfl Hcm Hap Hidx' Hnw2 Hst2 Hoff2 Hnc'
          Happlied Hpapplied Hcm2 Hss2 Hapg Hip2 Hipb2 Hpers2 Happlying Hpaused Hasz Hamx
          Hstor Hpend2 ?_ ?_
        $$ Hl HisStorage HStorage Husnap Hents Hents_cap Hl_logger Hu_logger
      all_goals rfl
    wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
    iapply HΦ $$ %li
    iframe Hlog Hes
    ipureintro
    exact ⟨Hsplit, Hli⟩

end proof

end EtcdGrove
end Perennial

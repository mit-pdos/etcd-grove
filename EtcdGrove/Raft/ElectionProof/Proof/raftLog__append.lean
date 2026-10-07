/-
Port of `election_proof/proof_raftLog__append.v`.
-/
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__append
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__lastIndex
import EtcdGrove.Raft.ElectionProof.Spec.unstable__truncateAndAppend

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

omit ffi [FfiInterp ffi] [FfiSemantics ext ffi] go_gctx in
private theorem isLoggerVal_open (x : GoInterface) :
    isLoggerVal (GF := GF) x ⊢ ∃ lg, ⌜x = interface.ok lg⌝ ∗ isLogger lg := by
  unfold isLoggerVal; exact .rfl

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

/-- Two exits. An empty batch returns `lastIndex()` with the log untouched. Otherwise
the `Panicf` is dead by the `committed` premise, `truncateAndAppend` gets the
`unstable` field (its offset is `prev.index + |sents| + 1`, `Hoffset`), and the log is
re-sealed at `logTruncateAppend`: same `stored`, the visible stable part cut at
`e0.Index` when the batch starts inside it. -/
theorem raftLog.append.wp_proof
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_unstable_truncateAndAppend : unstable.truncateAndAppend.spec (GF := GF) (hG := hG)) :
    raftLog.append.spec (GF := GF) (hG := hG) := by
  intro l ls ents es dq Hpre Hnorm
  obtain ⟨prev, sents, uents, lcm, lap, snap⟩ := ls
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
    wp_apply wp_raftLog_lastIndex _ ⟨prev, sents, uents, lcm, lap, snap⟩ $$ [$Hlog]
      as %li ⟨Hlog, %Hli⟩
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
    dsimp only at Hrange Hnwb
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
    iNamed Hcore
    dsimp only at *
    wp_auto
    rw [decide_eq_false (by rw [Hcm]; word)]
    wp_auto
    -- hand the `unstable` field to `truncateAndAppend`
    icases raftLog_split_unstable $$ Hl with ⟨Huf, Hlback⟩
    icases isLoggerVal_open _ $$ Hu_logger with ⟨%ulg, %Hulg, #Hulgr⟩
    have Hle' : uint.Z e0.Index' ≤ uint.Z lv.unstable'.offset' + (uents.length : Int) := by
      omega
    have Hnw' : uint.Z lv.unstable'.offset' + (uents.length : Int) < 2 ^ 64 := by omega
    -- the two adopt conditions agree
    have Hadopt_eq : (logAdopts ⟨prev, sents, uents, lcm, lap, snap⟩ (e0 :: ents') = true) =
        (uint.Z e0.Index' ≤ uint.Z lv.unstable'.offset' ∧
          uint.Z e0.Index' ≠ uint.Z lv.unstable'.offset' + (uents.length : Int)) := by
      simp only [logAdopts, decide_eq_true_eq, Hoffset]
      apply propext; omega
    simp only [Hadopt_eq]
    wp_apply wp_unstable_truncateAndAppend _ _ _ _ _ _ _ _ He0 Hle' Hnw' Hulg
        $$ [Huf Huents Huents_cap $Hes $Hulgr Hadopt]
      as %uv' ⟨Hun, %Huv', Hes⟩
    · unfold ownUnstable
      simp only [named]
      iframe Huf Huents Huents_cap Hadopt
    iNamed Hun
    ihave Hl := Hlback $$ Hu
    obtain ⟨Hoff', Hsnap', Hlg'⟩ := Huv'
    -- the new state
    have Hm : (uint.Z e0.Index' - uint.Z lv.unstable'.offset').toNat =
        (uint.Z e0.Index' - uint.Z prev.index' - 1 - (sents.length : Int)).toNat := by
      have : uint.Z e0.Index' - uint.Z lv.unstable'.offset' =
          uint.Z e0.Index' - uint.Z prev.index' - 1 - (sents.length : Int) := by
        rw [Hoffset]; omega
      rw [this]
    rw [Hm]
    have Hsplit := truncateAppend_split prev sents uents e0 ents'
    have Hprev : uint.Z prev.index' < uint.Z e0.Index' := by
      have := Happlied.1; rw [Hcm] at this; omega
    have Hlens' := truncateAppend_lengths prev sents uents e0 ents' (by omega) (by omega)
    have Hidx' : LogIndicesOk prev
        (sents.take (uint.Z e0.Index' - uint.Z prev.index' - 1).toNat ++
          (uents.take (uint.Z e0.Index' - uint.Z prev.index' - 1 - (sents.length : Int)).toNat
            ++ e0 :: ents')) := by
      rw [Hsplit]
      refine PlogWf_truncateAppend _ _ _ e0 Hidx He0 ⟨Hprev, ?_⟩ Hcontig
      simp only [plogLastIndexZ, List.length_append]; push_cast; omega
    have Hnc' : ∀ e ∈ sents.take (uint.Z e0.Index' - uint.Z prev.index' - 1).toNat ++
          (uents.take (uint.Z e0.Index' - uint.Z prev.index' - 1 - (sents.length : Int)).toNat
            ++ e0 :: ents'), e.Type' = EntryNormal := by
      intro e He
      simp only [List.mem_append] at He
      rcases He with He | He | He
      · exact HnoConfChange e (List.mem_append_left _ (List.mem_of_mem_take He))
      · exact HnoConfChange e (List.mem_append_right _ (List.mem_of_mem_take He))
      · exact Hnorm e He
    -- the storage relation: the visible stable part is cut, or -- with a snapshot
    -- pending -- stays empty
    have Hst2 : LogStoreOk snap sprev stored prev
        (sents.take (uint.Z e0.Index' - uint.Z prev.index' - 1).toNat)
        (uents.take (uint.Z e0.Index' - uint.Z prev.index' - 1 - (sents.length : Int)).toNat
          ++ e0 :: ents') := by
      cases snap with
      | some sid =>
        obtain ⟨Hp, Hs, Hsid⟩ := Hstore
        exact ⟨Hp, by rw [Hs]; simp, Hsid⟩
      | none =>
        obtain ⟨Hp, Hstored, -⟩ := Hstore
        exact ⟨Hp, (List.take_prefix _ _).trans Hstored, fun h => by simp at h⟩
    -- the storage's snapshot is at or below `committed`, so below the batch: its term
    -- survives the truncation
    have Hss2 : snap = none → StoredSnapOk ss lv.committed' prev
        (sents.take (uint.Z e0.Index' - uint.Z prev.index' - 1).toNat ++
          (uents.take (uint.Z e0.Index' - uint.Z prev.index' - 1 - (sents.length : Int)).toNat
            ++ e0 :: ents')) := by
      intro Hs
      rcases Hssnap Hs with H | ⟨Hsle, Hst⟩
      · exact .inl H
      · refine .inr ⟨Hsle, ?_⟩
        rw [Hsplit]
        exact plogTermAt_truncateAppend_below _ _ _ e0 _ _ He0 (by rw [Hcm] at Hsle; omega) Hst
    have Hls' : ((sents.take (uint.Z e0.Index' - uint.Z prev.index' - 1).toNat).length : Int)
        = min (uint.Z e0.Index' - uint.Z prev.index' - 1) (sents.length : Int) := by
      rw [List.length_take]; omega
    have Hnw2 : uint.Z prev.index'
        + ((sents.take (uint.Z e0.Index' - uint.Z prev.index' - 1).toNat).length : Int)
        + ((uents.take (uint.Z e0.Index' - uint.Z prev.index' - 1 - (sents.length : Int)).toNat
            ++ e0 :: ents').length : Int) + 1 < 2 ^ 64 := by
      simp only [List.length_cons] at Hnwb; push_cast at Hnwb; omega
    have Hoff2 : uint.Z uv'.offset' = uint.Z prev.index'
        + ((sents.take (uint.Z e0.Index' - uint.Z prev.index' - 1).toNat).length : Int) + 1 := by
      rw [Hoff', Hls', Hoffset]; omega
    have Hcm2 : uint.Z lv.committed' ≤ uint.Z prev.index'
        + ((sents.take (uint.Z e0.Index' - uint.Z prev.index' - 1).toNat).length : Int)
        + ((uents.take (uint.Z e0.Index' - uint.Z prev.index' - 1 - (sents.length : Int)).toNat
            ++ e0 :: ents').length : Int) := by
      rw [Hcm]; omega
    rw [← Hlg'] at Hulg
    rw [← Hsnap', ← Hlg']
    ihave Hlog : ownRaftLog l ⟨prev,
        sents.take (uint.Z e0.Index' - uint.Z prev.index' - 1).toNat,
        uents.take (uint.Z e0.Index' - uint.Z prev.index' - 1 - (sents.length : Int)).toNat
          ++ e0 :: ents', lcm, lap, snap⟩ $$ [Hl HStorage Hents Hents_cap]
    · iapply ownRaftLog_intro l { lv with unstable' := uv' } lv.storage' snap prev _ _ lcm lap
          sprev stored ss rfl Hcm Hap Hidx' Hnw2 Hst2 Hoff2 Hnc'
          Happlied Hpapplied Hcm2 Hss2
        $$ Hl HisStorage HStorage Husnap Hents Hents_cap Hl_logger Hu_logger
    wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
    iapply HΦ $$ %li
    simp only [logTruncateAppend]
    iframe Hlog Hes
    ipureintro
    exact ⟨Hsplit, Hli⟩

end proof

end EtcdGrove
end Perennial

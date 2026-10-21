/- Port of election_proof/proof_raftLog__stableTo.v (857d09190).

Lean notes: `stable_hit_unstable` is the private `stableHit_unstable`. -/
module

public import Spec.go_etcd_io.raft.v3.raftLog__stableTo
public import Spec.go_etcd_io.raft.v3.unstable__stableTo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The unstable struct's hit test is the log's: the suffix starts at `logOffset`, and
the log's term at an index of the suffix is the entry's. -/
private theorem stableHit_unstable [FfiSyntax] (lv : raftLog) (ls : LogState) (id : entryID)
    (Hoff : uint.Z lv.unstable'.offset' = logOffset ls) :
    StableHit ls id ↔ UnstableHit (unstableOf lv ls) id := by
  simp only [StableHit, UnstableHit, logOffset, plogTermAt] at Hoff ⊢
  rw [Hoff]
  have key : ∀ (h : uint.Z ls.prev.index' + (ls.sents.length : Int) + 1 ≤ uint.Z id.index'),
      (ls.sents ++ ls.uents)[(uint.Z id.index' - uint.Z ls.prev.index' - 1).toNat]?
        = ls.uents[(uint.Z id.index' - (uint.Z ls.prev.index' + (ls.sents.length : Int) + 1)).toNat]? := by
    intro h
    rw [List.getElem?_append_right (by omega)]
    congr 1
    omega
  constructor
  · rintro ⟨⟨h1, h2⟩, ht⟩
    rw [ite_eq_right (by omega), ite_eq_right (by omega), key h1] at ht
    refine ⟨⟨h1, by omega⟩, ?_⟩
    cases he : ls.uents[(uint.Z id.index' - (uint.Z ls.prev.index' + (ls.sents.length : Int) + 1)).toNat]?
      with
    | none => rw [he] at ht; cases ht
    | some e =>
      rw [he] at ht
      simp only [Option.map_eq_map, Option.map_some, Option.some.injEq] at ht
      exact ⟨e, rfl, ht⟩
  · rintro ⟨⟨h1, h2⟩, e, he, ht⟩
    refine ⟨⟨h1, by omega⟩, ?_⟩
    rw [ite_eq_right (by omega), ite_eq_right (by omega), key h1, he]
    simp [ht]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftLog.stableTo.wp_proof
    (wp_unstable_stableTo : unstable.stableTo.spec (GF := GF) (hG := hG)) :
    raftLog.stableTo.spec (GF := GF) (hG := hG) := by
  intro l ls id Hok
  wp_start as H
  iNamed H
  iNamed Hlog
  wp_auto
  -- (D22 S-d1b) a pending snapshot is `prev` (in the `sapp` window too, with a stable part
  -- after it), below the offset
  have Hsoff : ∀ sid, ls.snap = some sid →
      uint.Z sid.index' < uint.Z lv.unstable'.offset' := by
    intro sid Hs
    have Hpv : ls.prev = sid := by
      cases Hsa : ls.sapp
      · have Hv := snapV_of Hsa
        rw [Hv, Hs] at Hstore
        exact Hstore.1
      · have := (Hsappi Hsa).1
        rw [Hs] at this
        exact (Option.some.inj this).symm
    subst Hpv
    omega
  have Hnw' : uint.Z lv.unstable'.offset' + (ls.uents.length : Int) < 2^64 := by omega
  lend_unstable
  wp_apply wp_unstable_stableTo _ (unstableOf lv ls) id Hsoff Hnw' $$ [$Hun]
    as %us' ⟨Hun, %Hus'⟩
  obtain ⟨Hhit, Hmiss⟩ := Hus'
  iclear Husnap Hpksn Hu_logger
  icases ownUnstable_reopen _ _ _ $$ Hlback Hun
    with ⟨%uv', Hl, Huents_cap, Huents, #Husnap, #Hpksn, #Hu_logger, %Huoff, %Huoip, %Husip⟩
  iapply HΦ
  have Hiff := stableHit_unstable lv ls id Hoffset
  unfold logStableTo
  by_cases Hh : StableHit ls id
  · -- the hit: the persisted prefix moves stable
    rw [ite_eq_left Hh]
    obtain rfl := Hhit (Hiff.1 Hh)
    obtain ⟨Hsn0, Hup, Hsto⟩ := Hok Hh
    -- (D22 S-d1b) no snapshot pending, or the storage holds it (`sapp`): the storage relation is
    -- the one with none
    have Hsn : snapV ls = none := by
      rcases Hsn0 with h | h
      · cases Hsa : ls.sapp
        · rw [snapV_of Hsa]; exact h
        · exact snapV_sapp Hsa
      · exact snapV_sapp h
    obtain ⟨Hr, -⟩ := Hh
    obtain ⟨Hsp, Hsl, Hsu⟩ : LogStoreOk none σ ls.prev ls.sents ls.uents := Hsn ▸ Hstore
    have Hp := Hpersist Hsn
    rw [Hup] at Hp
    simp only [logOffset] at Hr ⊢
    have Hk : (uint.Z id.index' + 1 - uint.Z lv.unstable'.offset').toNat
        = (uint.Z id.index' + 1 - (uint.Z ls.prev.index' + (ls.sents.length : Int) + 1)).toNat := by
      omega
    generalize Hkdef : (uint.Z id.index' + 1
      - (uint.Z ls.prev.index' + (ls.sents.length : Int) + 1)).toNat = k at Hk ⊢
    have Hkb : 0 ≤ (k : Int) ∧ (k : Int) ≤ (ls.uents.length : Int) ∧
        0 ≤ uint.Z ls.inprogress - uint.Z lv.unstable'.offset' ∧
        uint.Z ls.inprogress - uint.Z lv.unstable'.offset' ≤ (ls.uents.length : Int) := by
      omega
    -- the storage holds the log up to `id`: the stable part and `k` unstable entries
    have Hst' : ls.stored = ls.sents ++ ls.uents.take k := by
      have Hn : (uint.Z id.index' - uint.Z ls.prev.index').toNat = ls.sents.length + k := by
        omega
      rw [Hsto, Hn, List.take_append, List.take_of_length_le (by omega),
        Nat.add_sub_cancel_left]
    have Hps := persist_stable σ ls.sents ls.uents ls.stored
      (uint.Z ls.inprogress - uint.Z lv.unstable'.offset') (k : Int) Hkb Hp
      (fun _ => by rw [Int.toNat_natCast]; exact Hst')
    rw [Int.toNat_natCast] at Hps
    reseal_raftLogW
    · rw [List.append_assoc, List.take_append_drop]; exact Hidx
    · simp only [List.length_append, List.length_take, List.length_drop]; omega
    · -- the storage relation
      show LogStoreOk (snapV ls) _ _ _ _
      rw [Hsn]
      exact ⟨Hsp, (List.prefix_append _ _).trans Hps.1.1, Hps.2⟩
    · simp only [Huoff, List.length_append, List.length_take]
      word
    · simp only [List.length_append, List.length_take, List.length_drop]
      omega
    · intro _
      rw [List.append_assoc, List.take_append_drop]
      exact Hssnap Hsn
    · simp only [Huoff, w64Max_spec, List.length_drop]
      word
    · intro _
      have Hipo : uint.Z (w64Max ls.inprogress (id.index' + W64 1)) - uint.Z (id.index' + W64 1)
          = max (uint.Z ls.inprogress - uint.Z lv.unstable'.offset') (k : Int) - (k : Int) := by
        rw [w64Max_spec]; word
      simp only [Huoff, Hipo, Hup]
      exact Hps.1
    · -- nothing pending: an acknowledgement that hits comes after the append
      exact ⟨Hpend.1, fun _ e0 He0 => by simp [Hup] at He0⟩
    · -- (D19i part 1) the floor: `offsetInProgress` only rises
      refine ⟨Hfl.1, Hfl.2.1, ?_, Hfl.2.2.2⟩
      have := Hfl.2.2.1
      have := w64Max_spec ls.inprogress (id.index' + W64 1)
      simp only
      omega
    · -- (D22 S-d1b) a snapshot in progress: the relation, from the storage's
      refine ⟨fun _ => ?_, fun Hs Hsp => ?_⟩
      · have Hipo : uint.Z (w64Max ls.inprogress (id.index' + W64 1)) - uint.Z (id.index' + W64 1)
            = max (uint.Z ls.inprogress - uint.Z lv.unstable'.offset') (k : Int) - (k : Int) := by
          rw [w64Max_spec]; word
        simp only [Huoff, Hipo]
        exact Hps.1.rel
      · -- (D22 S-d3a) a pending snapshot is in progress here (the storage holds it, `sapp`)
        exfalso
        rcases Hsn0 with h | h
        · exact Hs h
        · rw [(Hsappi h).2.1] at Hsp; cases Hsp
    · simp only [Hk]
  · -- a miss: nothing changes
    rw [ite_eq_right Hh]
    obtain rfl := Hmiss (fun H => Hh (Hiff.2 H))
    reseal_raftLogW

end proof

end EtcdGrove
end Perennial

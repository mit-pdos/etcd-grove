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
  simp only [StableHit, UnstableHit, logOffset, plogTermAt, unstableOf] at Hoff ⊢
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
    rw [if_neg (by omega), if_neg (by omega), key h1] at ht
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
    rw [if_neg (by omega), if_neg (by omega), key h1, he]
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
  have Hsoff : ∀ sid, ls.snap = some sid →
      uint.Z lv.unstable'.offset' = uint.Z sid.index' + 1 := by
    intro sid Hs
    obtain ⟨rfl, Hse, -⟩ : LogStoreOk (some sid) σ ls.prev ls.sents ls.uents := Hs ▸ Hstore
    rw [Hse, List.length_nil] at Hoffset
    omega
  have Hnw' : uint.Z lv.unstable'.offset' + (ls.uents.length : Int) < 2^64 := by omega
  lend_unstable
  wp_apply wp_unstable_stableTo _ (unstableOf lv ls) id Hsoff Hnw' $$ [$Hun]
    as %us' ⟨Hun, %Hus'⟩
  obtain ⟨Hhit, Hmiss⟩ := Hus'
  iclear Husnap Hu_logger
  icases ownUnstable_reopen _ _ _ $$ Hlback Hun
    with ⟨%uv', Hl, Huents_cap, Huents, #Husnap, #Hu_logger, %Huoff, %Huoip⟩
  iapply HΦ
  have Hiff := stableHit_unstable lv ls id Hoffset
  unfold logStableTo
  by_cases Hh : StableHit ls id
  · -- the hit: the persisted prefix moves stable
    rw [if_pos Hh]
    obtain rfl := Hhit (Hiff.1 Hh)
    obtain ⟨Hsn, Hidip, Hup⟩ := Hok Hh
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
    have Hkb : 0 ≤ (k : Int) ∧ (k : Int) ≤ uint.Z ls.inprogress - uint.Z lv.unstable'.offset' ∧
        uint.Z ls.inprogress - uint.Z lv.unstable'.offset' ≤ (ls.uents.length : Int) := by
      omega
    have Hps := persist_stable σ ls.sents ls.uents
      (uint.Z ls.inprogress - uint.Z lv.unstable'.offset') (k : Int) Hkb Hp
    rw [Int.toNat_natCast] at Hps
    reseal_raftLog
    · rw [List.append_assoc, List.take_append_drop]; exact Hidx
    · simp only [List.length_append, List.length_take, List.length_drop]; omega
    · -- the storage relation
      simp only [Hsn]
      refine ⟨Hsp, (List.prefix_append _ _).trans Hps.1, ?_⟩
      intro Hnil
      have Hk' : ls.uents.length ≤ k := List.drop_eq_nil_iff.mp Hnil
      rw [List.take_of_length_le Hk']
      exact Hp.2.1 (by omega)
    · simp only [Huoff, List.length_append, List.length_take]
      word
    · rw [List.append_assoc, List.take_append_drop]; exact HnoConfChange
    · simp only [List.length_append, List.length_take, List.length_drop]
      omega
    · intro _
      rw [List.append_assoc, List.take_append_drop]
      exact Hssnap Hsn
    · simp only [Huoff, w64Max_spec, List.length_drop]
      word
    · intro _
      have Hipo : uint.Z (w64Max ls.inprogress (id.index' + W64 1)) - uint.Z (id.index' + W64 1)
          = uint.Z ls.inprogress - uint.Z lv.unstable'.offset' - (k : Int) := by
        rw [w64Max_spec]; word
      simp only [Huoff, Hipo, Hup]
      exact Hps
    · simp only [unstableOf, Hk]
  · -- a miss: nothing changes
    rw [if_neg Hh]
    obtain rfl := Hmiss (fun H => Hh (Hiff.2 H))
    reseal_raftLog

end proof

end EtcdGrove
end Perennial

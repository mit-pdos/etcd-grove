/- Port of election_proof/proof_raftLog__stableTo.v (857d09190).

Lean notes: `stable_hit_unstable` is the private `stableHit_unstable`. -/
import EtcdGrove.Raft.Spec.raftLog__stableTo
import EtcdGrove.Raft.Spec.unstable__stableTo

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The unstable struct's hit test is the log's: the suffix starts at `logOffset`, and
the log's term at an index of the suffix is the entry's. -/
private theorem stableHit_unstable [FfiSyntax] (ls : LogState) (uv : unstable) (id : entryID)
    (_Hidx : LogIndicesOk ls.prev (ls.sents ++ ls.uents))
    (Hoff : uint.Z uv.offset' = logOffset ls) :
    StableHit ls id ↔ UnstableHit uv ls.uents id := by
  obtain ⟨prev, sents, uents, _, _, _, _, _, _, _, _⟩ := ls
  simp only [StableHit, UnstableHit, logOffset, plogTermAt] at Hoff ⊢
  rw [Hoff]
  have key : ∀ (h : uint.Z prev.index' + (sents.length : Int) + 1 ≤ uint.Z id.index'),
      (sents ++ uents)[(uint.Z id.index' - uint.Z prev.index' - 1).toNat]?
        = uents[(uint.Z id.index' - (uint.Z prev.index' + (sents.length : Int) + 1)).toNat]? := by
    intro h
    rw [List.getElem?_append_right (by omega)]
    congr 1
    omega
  constructor
  · rintro ⟨⟨h1, h2⟩, ht⟩
    rw [if_neg (by omega), if_neg (by omega), key h1] at ht
    refine ⟨⟨h1, by omega⟩, ?_⟩
    cases he : uents[(uint.Z id.index' - (uint.Z prev.index' + (sents.length : Int) + 1)).toNat]?
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftLog.stableTo.wp_proof
    (wp_unstable_stableTo : unstable.stableTo.spec (GF := GF) (hG := hG)) :
    raftLog.stableTo.spec (GF := GF) (hG := hG) := by
  intro l ls id Hok
  obtain ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ := ls
  wp_start as H
  iNamed H
  icases (ownRaftLog_unfold l prev sents uents lcm lap snap lip lapg lpend lasz lamx).1 $$ Hlog
    with ⟨%lv, Hl, %Hcm, %Hap, %Hapg, %Hip, %Hasz, %Hamx, Hcore⟩
  unfold ownRaftLogCore
  icases Hcore with ⟨%sprev, %stored, %ss, Hcore⟩
  iNamed Hcore
  wp_auto
  ihave #Hulgv : isLoggerVal lv.unstable'.logger' $$ [Hu_logger]
  · iexact Hu_logger
  iunfold isLoggerVal at Hulgv
  icases Hulgv with ⟨%ulg, %Hulg, #Hulgr⟩
  icases raftLog_split_unstable l lv $$ Hl with ⟨Huf, Hlback⟩
  have Hsoff : ∀ sid, snap = some sid →
      uint.Z lv.unstable'.offset' = uint.Z sid.index' + 1 := by
    intro sid Hs
    subst Hs
    obtain ⟨rfl, rfl, -⟩ := Hstore
    simp only [List.length_nil] at Hoffset
    omega
  have Hnw' : uint.Z lv.unstable'.offset' + (uents.length : Int) < 2^64 := by omega
  wp_apply wp_unstable_stableTo _ _ _ snap id ulg Hsoff Hnw' Hulg $$ [Huf Huents Huents_cap]
    as %uv' %uents' ⟨Hun, %Huv'⟩
  · unfold ownUnstable
    simp only [named]
    iframe # ∗
  obtain ⟨Hsnap', Hlg', Hhit, Hmiss⟩ := Huv'
  unfold ownUnstable
  icases Hun with ⟨Hu, Huents_cap, Huents⟩
  ihave Hl := Hlback $$ Hu
  iapply HΦ
  rw [← Hlg'] at *
  rw [← Hsnap'] at *
  have Hiff := stableHit_unstable ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩
    lv.unstable' id Hidx Hoffset
  unfold logStableTo
  by_cases Hh : StableHit ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ id
  · -- the hit: the persisted prefix moves stable
    rw [if_pos Hh]
    obtain ⟨rfl, Hoff', Hip'⟩ := Hhit (Hiff.1 Hh)
    obtain ⟨Hsn, Hidip, Hup⟩ := Hok Hh
    simp only at Hsn Hidip Hup
    subst snap lpend
    obtain ⟨Hr, -⟩ := Hh
    simp only [logOffset] at Hr ⊢
    rw [show (uint.Z id.index' + 1 - uint.Z lv.unstable'.offset').toNat
      = (uint.Z id.index' + 1 - (uint.Z prev.index' + (sents.length : Int) + 1)).toNat
      by omega]
    generalize Hkdef : (uint.Z id.index' + 1 - (uint.Z prev.index' + (sents.length : Int) + 1)).toNat = k
    have Hkb : 0 ≤ (k : Int) ∧ (k : Int) ≤ uint.Z lip - uint.Z lv.unstable'.offset' ∧
        uint.Z lip - uint.Z lv.unstable'.offset' ≤ (uents.length : Int) := by
      subst lip; omega
    obtain ⟨rfl, Hsl, Hsu⟩ := Hstore
    obtain ⟨Hpre, Heq, Hpe⟩ := Hpersist rfl
    rw [Hip] at Hpre Heq
    have Hps := persist_stable sprev stored sents uents
      (uint.Z lip - uint.Z lv.unstable'.offset') (k : Int) Hkb ⟨Hpre, Heq, Hpe⟩
    rw [Int.toNat_natCast] at Hps
    reseal_raftLog
    · rw [List.append_assoc, List.take_append_drop]; exact Hidx
    · simp only [List.length_append, List.length_take, List.length_drop]; omega
    · -- the storage relation
      refine ⟨rfl, (List.prefix_append _ _).trans Hps.1, ?_⟩
      intro Hnil
      have Hk : uents.length ≤ k := List.drop_eq_nil_iff.mp Hnil
      rw [List.take_of_length_le Hk]
      exact Heq (by omega)
    · dsimp only
      rw [Hoff']
      simp only [List.length_append, List.length_take]
      word
    · rw [List.append_assoc, List.take_append_drop]; exact HnoConfChange
    · dsimp only
      simp only [List.length_append, List.length_take, List.length_drop]
      omega
    · intro _
      dsimp only
      rw [List.append_assoc, List.take_append_drop]
      exact Hssnap rfl
    · dsimp only; rw [Hip', Hip]
    · dsimp only
      rw [Hip', Hoff', w64Max_spec]
      simp only [List.length_drop]
      word
    · intro _
      dsimp only
      rw [Hip', Hoff', w64Max_spec,
        show max (uint.Z lv.unstable'.offsetInProgress') (uint.Z (id.index' + W64 1))
            - uint.Z (id.index' + W64 1)
          = uint.Z lip - uint.Z lv.unstable'.offset' - (k : Int) by subst lip; word]
      exact Hps
  · -- a miss: nothing changes
    rw [if_neg Hh]
    obtain ⟨rfl, rfl⟩ := Hmiss (fun H => Hh (Hiff.2 H))
    reseal_raftLog

end proof

end EtcdGrove
end Perennial

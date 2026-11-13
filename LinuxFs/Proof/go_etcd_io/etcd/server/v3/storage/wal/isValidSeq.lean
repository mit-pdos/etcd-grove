/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/isValidSeq.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.isValidSeq
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.searchIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.isValidSeq.wp_proof
    (HParse : go_etcd_io.etcd.server.v3.storage.wal.parseWALName.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.isValidSeq.spec (GF := GF) (hG := hG) := by
  intro lg sl names dq hnames
  wp_start as Hsl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  have hl : (names.length : Int) = sint.Z sl.len := by rw [Hlen.1]; word
  ihave IH : iprop(∃ (j : w64) (lv : w64) (nv : GoString),
      "i" ∷ i_ptr ↦ j ∗ "lastSeq" ∷ lastSeq_ptr ↦ lv ∗ "name" ∷ name_ptr ↦ nv ∗
      "Hsl" ∷ sl ↦*{dq} names ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ names.length ∧
        walSeqOk 0 (names.map walNameSeq) =
          walSeqOk lv ((names.map walNameSeq).drop (sint.nat j))⌝) $$ [i lastSeq name Hsl]
  · iexists W64 0, W64 0, _
    simp only [named]
    iframe
    ipureintro
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0]
    refine ⟨by decide, by simp, by simp⟩
  wp_for IH
  obtain ⟨Hj0, Hjl, Hjs⟩ := Hj
  wp_if_destruct
  · have hjl : sint.nat j < names.length := by
      have : sint.Z j < sint.Z sl.len := Hif
      word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj0, by word⟩)]
    obtain ⟨n, hn⟩ : ∃ n, names[sint.nat j]? = some n := ⟨_, List.getElem?_eq_getElem hjl⟩
    wp_apply wp_load_slice_index sl (sint.Z j) names dq n Hj0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hn
    try wp_auto
    obtain ⟨sq, ix, rfl⟩ := hnames n (List.mem_of_getElem? hn)
    wp_apply HParse (fmt.walNameStr sq ix) as %seq %idx %err %Hp
    obtain ⟨rfl, rfl, rfl⟩ := Hp.1 sq ix (walNameStr_suffix sq ix) (fmt.scanWalName_walNameStr sq ix)
    try wp_auto
    have hdrop : (names.map walNameSeq).drop (sint.nat j) =
        seq :: (names.map walNameSeq).drop (sint.nat j + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hjl)]
      congr 1
      simp only [List.getElem_map]
      rw [(List.getElem?_eq_some_iff.1 hn).2]
      simp [walNameSeq, fmt.scanWalName_walNameStr]
    rw [hdrop] at Hjs
    wp_if_destruct
    · wp_for_post
      iframe
      iexists j + W64 1, seq, _
      simp only [named]
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [Hjs, show sint.nat (j + W64 1) = sint.nat j + 1 by word, walSeqOk, ite_eq_right (fun h => h.1 rfl)]
    · have hlv0 : ¬ lv = W64 0 := Hif
      wp_if_destruct
      · try wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, seq, _
        simp only [named]
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [Hjs, show sint.nat (j + W64 1) = sint.nat j + 1 by word, walSeqOk, ite_eq_right (fun h => h.2 rfl)]
      · try wp_auto
        wp_for_post
        have hy : lv ≠ 0 ∧ lv ≠ seq - 1 := ⟨fun h => hlv0 (by rw [h]; rfl), fun h => Hif (by rw [h]; rfl)⟩
        rw [Hjs, walSeqOk, ite_eq_left hy]
        iapply HΦ
        iframe
  · have hj : sint.nat j = names.length := by
      have : ¬ sint.Z j < sint.Z sl.len := Hif
      word
    rw [hj, show names.length = (names.map walNameSeq).length by simp, List.drop_length,
      walSeqOk] at Hjs
    try wp_auto
    rw [Hjs]
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial

/-
Port of `election_proof/proof_raftLog__findConflict.v`.
-/
import EtcdGrove.Raft.Spec.raftLog__findConflict
import EtcdGrove.Raft.Spec.pbEntryID
import EtcdGrove.Raft.Spec.raftLog__matchTerm
import EtcdGrove.Raft.Spec.raftLog__lastIndex
import EtcdGrove.Raft.Spec.raftLog__term
import EtcdGrove.Raft.Spec.raftLog__zeroTermOnOutOfBounds

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

/-- `isLoggerVal`, opened (as in `Proof/raftLog__restore.lean`). -/
private theorem isLoggerVal_open (x : GoInterface) :
    isLoggerVal (GF := GF) x ⊢ ∃ lg, ⌜x = interface.ok lg⌝ ∗ isLogger lg := by
  unfold isLoggerVal; exact .rfl

/-- The loop invariant: the prefix scanned so far matched, so the answer is
`plogFindConflict` of what is left (`Hfc`). The `for range` allocates its own counter
besides the Go-level `i` (notes/gotchas.md), so both are in the invariant. -/
theorem raftLog.findConflict.wp_proof
    (wp_pbEntryID : pbEntryID.spec (GF := GF) (hG := hG))
    (wp_raftLog_matchTerm : raftLog.matchTerm.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_term : raftLog.term.spec (GF := GF) (hG := hG))
    (wp_raftLog_zeroTermOnOutOfBounds :
      raftLog.zeroTermOnOutOfBounds.spec (GF := GF) (hG := hG)) :
    raftLog.findConflict.spec (GF := GF) (hG := hG) := by
  intro l ls es dq ents Hge
  obtain ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ := ls
  wp_start as ⟨Hlog, Hes⟩
  iNamed Hlog
  iNamed Hes
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hes
  -- the `for range` counter is `i_ptr`; the Go-level `i` (written from `$key`) is the
  -- inaccessible one
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
  dsimp only at Hge ⊢
  ihave IH : iprop(∃ (n k : w64),
      "Hj" ∷ i_ptr ↦ n ∗
      "Hgi" ∷ gi_ptr ↦ k ∗
      "Hlog" ∷ ownRaftLog l ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ ∗
      "Hes" ∷ es ↦*{dq} ents ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ents.length : Int)⌝ ∗
      "%Hfc" ∷ ⌜plogFindConflict prev (sents ++ uents) ents
                 = plogFindConflict prev (sents ++ uents) (ents.drop (sint.nat n))⌝)
      $$ [i Hgi Hlog Hes]
  · iexists W64 0, zero_val w64
    iframe
    ipureintro
    exact ⟨by word, rfl⟩
  wp_for IH
  wp_if_destruct
  · list_elem ents (sint.nat n) as e
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index es (sint.Z n) ents dq e Hn.1 $$ [Hes] with Hes
    · iframe
      ipureintro
      exact He_lookup
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    icases ownSlice_elem_acc (sint.Z n) e es dq ents Hn.1 He_lookup $$ Hes with ⟨He, Hesback⟩
    wp_apply wp_pbEntryID $$ [$He] as He
    ihave Hes := Hesback $$ %e He
    have Hset : ents.set (sint.Z n).toNat e = ents := by
      have hlt : (sint.Z n).toNat < ents.length := by word
      have hget : ents[(sint.Z n).toNat]'hlt = e := by
        have h2 : ents[(sint.Z n).toNat]? = some e := He_lookup
        rw [List.getElem?_eq_getElem hlt] at h2; exact Option.some.inj h2
      rw [← hget]; exact List.set_getElem_self hlt
    rw [Hset]
    wp_apply wp_raftLog_matchTerm l _ (entId e) $$ [$Hlog] as %b ⟨Hlog, %Hb⟩
    have Hdrop : ents.drop (sint.nat n) = e :: ents.drop (sint.nat n + 1) := by
      have hlt : sint.nat n < ents.length := by word
      rw [List.drop_eq_getElem_cons hlt]
      congr
      rw [List.getElem?_eq_getElem hlt] at He_lookup; exact Option.some.inj He_lookup
    cases b
    · -- the first conflict: return its index
      have Hres : plogFindConflict prev (sents ++ uents) ents = e.Index' := by
        rw [Hfc, Hdrop]
        have hm : ¬ PlogMatches prev (sents ++ uents) (entId e) := by simpa using Hb.symm
        simp only [plogFindConflict, hm, ↓reduceIte]
      have Hgee : uint.Z prev.index' ≤ uint.Z e.Index' :=
        Hge e (List.mem_of_getElem? He_lookup)
      wp_auto
      wp_apply wp_raftLog_lastIndex l _ $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
      dsimp only at Hli
      wp_if_destruct
      · -- `id.index <= lastIndex()`: the `Infof`
        wp_apply wp_raftLog_term l _ e.Index' $$ [$Hlog] as %t %err ⟨Hlog, %Herr, -, -⟩
        have Herr0 : err = interface.nil := Herr.2 (by dsimp only; exact ⟨Hgee, by omega⟩)
        subst Herr0
        wp_apply wp_raftLog_zeroTermOnOutOfBounds l t interface.nil $$ [] as %t' -
        · ileft; ipureintro; rfl
        wp_apply wp_slice_literal
        try (isplitr; (ipureintro; rfl))
        try iintro %_ ⟨_, -⟩
        try wp_auto
        iNamed Hlog
        iNamed Hcore
        dsimp only at *
        icases isLoggerVal_open _ $$ Hl_logger with ⟨%lg, %Hlg, #Hlgr⟩
        wp_auto
        -- the logger is loaded: re-seal before `rw [Hlg]`, which would also rewrite the
        -- `Hl_logger` the re-seal needs
        ihave Hlog : ownRaftLog l ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ $$
          [Hl HStorage Huents Huents_cap]
        · reseal_raftLog
        rw [Hlg]
        wp_apply Logger.wp_logf lg _ _ _ (by decide) $$ Hlgr
        wp_for_post
        rw [← Hres]
        iapply HΦ
        iframe
      · wp_for_post
        rw [← Hres]
        iapply HΦ
        iframe
    · -- the entry matches: keep scanning
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, n
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      rw [Hfc, Hdrop]
      have hm : PlogMatches prev (sents ++ uents) (entId e) := by simpa using Hb.symm
      simp only [plogFindConflict, hm, ↓reduceIte]
      congr 2
      word
  · -- the whole batch matched
    have Hnil : ents.drop (sint.nat n) = [] := List.drop_eq_nil_of_le (by word)
    rw [Hnil] at Hfc
    rw [Hfc, show plogFindConflict prev (sents ++ uents) [] = W64 0 from rfl]
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial

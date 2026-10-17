/-
Port of `election_proof/proof_raftLog__findConflict.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.raftLog__findConflict
public import Spec.go_etcd_io.raft.v3.pbEntryID
public import Spec.go_etcd_io.raft.v3.raftLog__matchTerm
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.raftLog__term
public import Spec.go_etcd_io.raft.v3.raftLog__zeroTermOnOutOfBounds

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

/-- `isLoggerVal`, opened (as in `Proof/raftLog__restore.lean`). -/
private theorem isLoggerVal_open (x : GoInterface) :
    isLoggerVal (GF := GF) x ⊢ ∃ lg, ⌜x = interface.ok lg⌝ ∗ isLogger lg := by
  unfold isLoggerVal; exact .rfl

/-- First the `prev` check; then the loop invariant: the scan so far matched, `match` holds
`m`, and the answer is `plogFindMatch` from `m` of what is left (`Hfm`). The `for range`
allocates its own counter besides the Go-level `i` (notes/gotchas.md), so both are in the
invariant. -/
theorem raftLog.findConflict.wp_proof
    (wp_pbEntryID : pbEntryID.spec (GF := GF) (hG := hG))
    (wp_raftLog_matchTerm : raftLog.matchTerm.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raftLog_term : raftLog.term.spec (GF := GF) (hG := hG))
    (wp_raftLog_zeroTermOnOutOfBounds :
      raftLog.zeroTermOnOutOfBounds.spec (GF := GF) (hG := hG)) :
    raftLog.findConflict.spec (GF := GF) (hG := hG) := by
  intro l ls s dq ents Hwf
  wp_start as ⟨Hlog, Hes⟩
  wp_auto
  wp_apply wp_raftLog_matchTerm l _ s.prev' $$ [$Hlog] as %b0 ⟨Hlog, %Hb0⟩
  cases b0
  · -- `s.prev` does not match: `(entryID{}, false)`
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    exact ⟨Hb0, fun h => (by cases h), fun _ => rfl⟩
  have Hpm : PlogMatches ls.prev (ls.sents ++ ls.uents) s.prev' := of_decide_eq_true Hb0.symm
  have Hprange := plogTermAt_some_range _ _ _ _ Hpm
  wp_auto
  ihave %Hlen := entsPts_len _ _ _ $$ Hes
  -- the `for range` counter is `i_ptr`; the Go-level `i` (written from `$key`) is the
  -- inaccessible one
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
  ihave IH : iprop(∃ (n k : w64) (m : entryID),
      "Hj" ∷ i_ptr ↦ n ∗
      "Hgi" ∷ gi_ptr ↦ k ∗
      "Hm" ∷ match_ptr ↦ m ∗
      "Hs" ∷ s_ptr ↦ s ∗
      "Hlog" ∷ ownRaftLog l ls ∗
      "Hes" ∷ entsPts s.entries' dq ents ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ents.length : Int)⌝ ∗
      "%Hfm" ∷ ⌜plogFindMatch ls.prev (ls.sents ++ ls.uents) s.prev' ents
                 = plogFindMatch ls.prev (ls.sents ++ ls.uents) m (ents.drop (sint.nat n))⌝)
      $$ [i Hgi «match» s Hlog Hes]
  · iexists W64 0, zero_val w64, s.prev'
    iframe
    ipureintro
    exact ⟨by word, rfl⟩
  wp_for IH
  wp_if_destruct
  · list_elem ents (sint.nat n) as e
    iunfold entsPts at Hes
    icases Hes with ⟨%lps, Hsl, #Hb⟩
    icases entsBig_lookup lps ents (sint.nat n) e He_lookup $$ Hb with ⟨%lp, %Hlp, #He⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index s.entries' (sint.Z n) lps dq lp Hn.1 $$ [Hsl] with Hsl
    · iframe
      ipureintro
      exact Hlp
    rw [ite_eq_left_of_eq_true _ _ (eq_true (by word))]
    wp_apply wp_load_slice_index s.entries' (sint.Z n) lps dq lp Hn.1 $$ [Hsl] with Hsl
    · iframe
      ipureintro
      exact Hlp
    wp_apply wp_pbEntryID $$ [$He] as -
    ihave Hes : entsPts s.entries' dq ents $$ [Hsl]
    · iunfold entsPts
      iexists lps
      iframe Hsl Hb
    wp_apply wp_raftLog_matchTerm l _ (entId e) $$ [$Hlog] as %b ⟨Hlog, %Hb⟩
    have Hdrop : ents.drop (sint.nat n) = e :: ents.drop (sint.nat n + 1) := by
      have hlt : sint.nat n < ents.length := by word
      rw [List.drop_eq_getElem_cons hlt]
      congr
      rw [List.getElem?_eq_getElem hlt] at He_lookup; exact Option.some.inj He_lookup
    cases b
    · -- the first entry the log does not have: return the last match
      have hm : ¬ PlogMatches ls.prev (ls.sents ++ ls.uents) (entId e) := by simpa using Hb.symm
      have Hres : plogFindMatch ls.prev (ls.sents ++ ls.uents) s.prev' ents = m := by
        rw [Hfm, Hdrop]
        simp only [plogFindMatch, hm, ↓reduceIte]
      have Hgee : uint.Z ls.prev.index' ≤ uint.Z e.Index' := by
        have := Hwf _ _ He_lookup
        omega
      wp_auto
      wp_apply wp_raftLog_lastIndex l _ $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
      wp_if_destruct
      · -- `id.index <= lastIndex()`: the `Infof`
        wp_apply wp_raftLog_term l _ e.Index' $$ [$Hlog] as %t %err ⟨Hlog, %Herr, -, -⟩
        have Herr0 : err = interface.nil := Herr.2 ⟨Hgee, by omega⟩
        subst Herr0
        wp_apply wp_raftLog_zeroTermOnOutOfBounds l t interface.nil $$ [] as %t' -
        · ileft; ipureintro; rfl
        wp_apply wp_slice_literal
        try (isplitr; (ipureintro; rfl))
        try iintro %_ ⟨_, -⟩
        try wp_auto
        iNamed Hlog
        icases isLoggerVal_open _ $$ Hl_logger with ⟨%lg, %Hlg, #Hlgr⟩
        wp_auto
        -- the logger is loaded: re-seal before `rw [Hlg]`, which would also rewrite the
        -- `Hl_logger` the re-seal needs
        ihave Hlog : ownRaftLog l ls $$
          [Hl HStorage Huents Huents_cap]
        · reseal_raftLog
        rw [Hlg]
        wp_apply Logger.wp_logf lg _ _ _ (by decide) $$ Hlgr
        wp_for_post
        iapply HΦ
        iframe
        ipureintro
        exact ⟨Hb0, fun _ => Hres.symm, fun h => (by cases h)⟩
      · wp_for_post
        iapply HΦ
        iframe
        ipureintro
        exact ⟨Hb0, fun _ => Hres.symm, fun h => (by cases h)⟩
    · -- the entry matches: `match = id`, keep scanning
      have hm : PlogMatches ls.prev (ls.sents ++ ls.uents) (entId e) := by simpa using Hb.symm
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, n, entId e
      iframe
      ipureintro
      refine ⟨by word, ?_⟩
      rw [Hfm, Hdrop]
      simp only [plogFindMatch, hm, ↓reduceIte]
      congr 2
      word
  · -- the whole slice matched
    have Hnil : ents.drop (sint.nat n) = [] := List.drop_eq_nil_of_le (by word)
    rw [Hnil] at Hfm
    iapply HΦ
    iframe
    ipureintro
    exact ⟨Hb0, fun _ => Hfm.symm, fun h => (by cases h)⟩

end proof

end EtcdGrove
end Perennial

/- Lean-first (no Rocq counterpart). The proof of `member.resume`. -/
module

public import WalTester.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.member__resume
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RefLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem member.resume.wp_proof : member.resume.spec (GF := GF) (hG := hG) := by
  intro m vc c t vo cm b l tm
  wp_start as ⟨#Hc, Ht, Hv, Hcm, Hb, Hl, Htm⟩
  iunfold contentsRep at Hc
  icases Hc with ⟨%Hcf, #Hce⟩
  obtain ⟨hh, hi, ht⟩ := Hcf
  ihave %Hel := ownSlice_len $$ Hce
  wp_auto
  wp_if_destruct
  all_goals
    ihave Ht : m.[member, go!"term"] ↦ tResumeTerm c $$ [Ht]
    · unfold tResumeTerm
      rw [← hh]
      first | rw [if_pos Hif] | rw [if_neg Hif]
      iexact Ht
    wp_apply (wp_map_make1 (K := w64) (V := w64) go.uint64 go.uint64) as %mp Hmp
    wp_apply (wp_mapInsert go.uint64 mp _ vc.baseIdx' vc.baseTerm') $$ [$Hmp] as Hmp
    rw [hi, ht]
    ihave HI : (∃ (i : w64),
        "i" ∷ i_ptr ↦ i ∗
        "Hl" ∷ m.[member, go!"last"] ↦ (c.ents.take (sint.nat i)).foldl (fun _ e => e.index') c.baseIdx ∗
        "Hmp" ∷ mp ↦$ (c.ents.take (sint.nat i)).foldl (fun M e => <[e.index' := e.term']> M)
          (<[c.baseIdx := c.baseTerm]> (∅ : GMap w64 w64)) ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z vc.ents'.len⌝ : IProp GF) $$ [i Hl Hmp]
    · iexists W64 0
      rw [show sint.nat (W64 0) = 0 from rfl]
      simp only [List.take_zero, List.foldl_nil]
      iframe
      ipureintro; constructor <;> word
    wp_for HI
    by_cases hlt : sint.Z i < sint.Z vc.ents'.len
    · rw [if_pos (by simp [hlt])]
      have hil : sint.nat i < c.ents.length := by
        have : sint.nat i < sint.nat vc.ents'.len := by word
        omega
      obtain ⟨x, Hx⟩ : ∃ x, c.ents[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hil⟩
      have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z vc.ents'.len := ⟨Hi.1, hlt⟩
      icases ownSlice_elem_acc (sint.Z i) x vc.ents' DFrac.discard c.ents Hi.1
        (by simpa [sint.nat] using Hx) $$ Hce with ⟨Hxv, -⟩
      iStructNamed Hxv
      wp_auto
      iterate 6 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
      wp_apply (wp_mapInsert go.uint64 mp _ x.index' x.term') $$ [$Hmp] as Hmp
      iterate 6 (try simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
      wp_for_post
      iframe
      iexists i + W64 1
      have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [hi1, foldl_take_succ _ _ _ _ _ Hx, foldl_take_succ _ _ _ _ _ Hx]
      iframe
      ipureintro; constructor <;> word
    · simp only [hlt, decide_false, _root_.decide_true, Bool.false_eq_true, ↓reduceIte, val_false_ne_true,
        not_false_eq_true]
      have hin : sint.nat i = c.ents.length := by
        have : sint.nat i = sint.nat vc.ents'.len := by word
        omega
      rw [hin, List.take_length]
      wp_auto
      rw [hh]
      wp_if_destruct
      all_goals
        iapply HΦ
        unfold tResumeCommit tResumeLast tResumeTerms
        by_cases hc : uint.nat (List.foldl (fun _ e => e.index') c.baseIdx c.ents) < uint.nat c.hs.commit'
        · rw [if_pos hc]
          first | (exfalso; have := Hif; word) | iframe
        · rw [if_neg hc]
          first | (exfalso; have := Hif; word) | iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial

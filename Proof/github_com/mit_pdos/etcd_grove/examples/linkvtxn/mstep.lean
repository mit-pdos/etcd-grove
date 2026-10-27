/-
Lean-first (no Rocq counterpart).

The proof of `mstep`: by the input's kind; a list's loop builds the key-values, a transaction's
loop evaluates the comparisons, then `runOps` on the branch.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.mstep
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.lookup
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.put
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.delKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.holds
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.runOps
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.cmpsOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.thenOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.elseOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.withRes
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.withKVs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem mstep.wp_proof (wp_lookup : lookup.spec (GF := GF) (hG := hG))
    (wp_put : put.spec (GF := GF) (hG := hG)) (wp_delKey : delKey.spec (GF := GF) (hG := hG))
    (wp_holds : holds.spec (GF := GF) (hG := hG)) (wp_runOps : runOps.spec (GF := GF) (hG := hG))
    (wp_cmpsOf : cmpsOf.spec (GF := GF) (hG := hG)) (wp_thenOf : thenOf.spec (GF := GF) (hG := hG))
    (wp_elseOf : elseOf.spec (GF := GF) (hG := hG)) (wp_withRes : withRes.spec (GF := GF) (hG := hG))
    (wp_withKVs : withKVs.spec (GF := GF) (hG := hG)) :
    mstep.spec (GF := GF) (hG := hG) := by
  intro x s g
  wp_start as ⟨#Hs, %Hb⟩
  unfold storeOwn
  icases Hs with ⟨#Hk, %Hr⟩
  ihave %Hl := ownSlice_len $$ Hk
  wp_auto
  irename : (in_ptr ↦ x : IProp GF) => Hin
  wp_if_destruct
  · -- a get
    wp_apply wp_lookup s.kvs' g.kvs _ x.Key' $$ [$Hk] as %v %ok ⟨-, %Hlk⟩
    iapply HΦ
    have e : mstepL x g = (g, { zOut with Rev' := g.rev, Found' := ok, R' := v }) := by
      unfold mstepL; rw [if_pos Hif, ← Hlk]
    rw [e, ← Hr]
    simp only
    isplit
    · isplit
      · iexact Hk
      · ipureintro; first | rfl | trivial
    · ipureintro; first | rfl | trivial
  · have H0 := Hif; clear Hif
    wp_if_destruct
    · -- a list
      have Hk1 := Hif; clear Hif
      wp_apply wp_slice_make3 (V := KV) (W64 0) s.kvs'.len ⟨by word, by word⟩
        as %o0 ⟨Ho, Hocap, -⟩
      rw [List.replicate_zero]
      ihave HI : (∃ (j : w64) (e0 : entry) (o : GoSlice),
          "i" ∷ i_ptr ↦ j ∗ "e" ∷ e_ptr ↦ e0 ∗ "kvs" ∷ kvs_ptr ↦ o ∗
          "Ho" ∷ o ↦* (g.kvs.take (sint.nat j)).map (fun e => (⟨e.key', e.r'⟩ : KV)) ∗
          "Hocap" ∷ ownSliceCap KV o (DFrac.own 1) ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.kvs'.len⌝ : IProp GF)
        $$ [i e kvs Ho Hocap]
      · iexists W64 0, _, o0
        rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil]
        iframe
        ipureintro; word
      wp_for HI
      by_cases Hif : sint.Z j < sint.Z s.kvs'.len
      · (try simp only [decide_eq_true Hif, ↓reduceIte]); wp_pures; cleanup_bool_decide
        (try wp_auto); cleanup_bool_decide
        have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.kvs'.len := ⟨Hj.1, Hif⟩
        simp only [Hb', _root_.and_self, ↓reduceIte]
        list_elem g.kvs (sint.nat j) as w
        wp_apply wp_load_slice_index s.kvs' (sint.Z j) g.kvs _ w Hj.1 $$ [Hk] as -
        · isplit
          · iexact Hk
          · ipureintro; exact Hw_lookup
        wp_apply wp_slice_literal (l := [(⟨w.key', w.r'⟩ : KV)])
        isplitr
        · ipureintro; first | rfl | trivial
        iintro %lsl ⟨Hl1, _⟩
        wp_apply wp_slice_append $$ [$Ho $Hocap $Hl1] as %o' ⟨Ho, Hocap, -⟩
        wp_for_post
        iframe
        iexists j + W64 1, _, o'
        rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hw_lookup]
        simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
        iframe
        ipureintro; word
      · (try simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte]); wp_pures
        cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
        have hall : g.kvs.take (sint.nat j) = g.kvs := List.take_of_length_le (by word)
        rw [hall]
        wp_apply wp_withKVs _ _ _ _ $$ [$Ho] as %out ⟨-, %Hout⟩
        iapply HΦ
        have e : mstepL x g = (g, withKVsL { zOut with Rev' := g.rev }
            (g.kvs.map fun e => (⟨e.key', e.r'⟩ : KV))) := by
          unfold mstepL; rw [if_neg H0, if_pos Hk1]
        rw [e, Hout, ← Hr]
        simp only
        isplit
        · isplit
          · iexact Hk
          · ipureintro; first | rfl | trivial
        · ipureintro; first | rfl | trivial
    · have H1 := Hif; clear Hif
      wp_if_destruct
      · -- a put
        have Hk2 := Hif; clear Hif
        wp_apply +noauto wp_put s.kvs' g.kvs _ (s.rev' + W64 1) x.Key' x.Val' $$ [$Hk] as %nk ⟨-, Hnk, -⟩
        · ipureintro; omega
        ipersist Hnk
        wp_auto
        iapply HΦ
        have e : mstepL x g = (⟨putL g.kvs (g.rev + W64 1) x.Key' x.Val', g.rev + W64 1⟩,
            { zOut with Rev' := g.rev + W64 1 }) := by
          unfold mstepL; rw [if_neg H0, if_neg H1, if_pos Hk2]
        rw [e, ← Hr]
        simp only
        isplit
        · isplit
          · iexact Hnk
          · ipureintro; first | rfl | trivial
        · ipureintro; first | rfl | trivial
      · have H2 := Hif; clear Hif
        wp_if_destruct
        · -- a delete
          have Hk3 := Hif; clear Hif
          wp_apply wp_lookup s.kvs' g.kvs _ x.Key' $$ [$Hk] as %v %ok ⟨-, %Hlk⟩
          wp_if_destruct
          · iapply HΦ
            have e : mstepL x g = (g, { zOut with Rev' := g.rev, N' := W64 0 }) := by
              unfold mstepL; rw [if_neg H0, if_neg H1, if_neg H2, if_pos Hk3,
                if_neg (by rw [← Hlk]; simp)]
            rw [e, ← Hr]
            simp only
            isplit
            · isplit
              · iexact Hk
              · ipureintro; first | rfl | trivial
            · ipureintro; first | rfl | trivial
          · wp_apply +noauto wp_delKey s.kvs' g.kvs _ x.Key' $$ [$Hk] as %nk ⟨-, Hnk, -⟩
            ipersist Hnk
            wp_auto
            iapply HΦ
            have e : mstepL x g = (⟨delKeyL g.kvs x.Key', g.rev + W64 1⟩,
                { zOut with Rev' := g.rev + W64 1, N' := W64 1 }) := by
              unfold mstepL; rw [if_neg H0, if_neg H1, if_neg H2, if_pos Hk3, if_pos (by rw [← Hlk])]
            rw [e, ← Hr]
            simp only
            isplit
            · isplit
              · iexact Hnk
              · ipureintro; first | rfl | trivial
            · ipureintro; first | rfl | trivial
        · have H3 := Hif; clear Hif
          wp_apply wp_cmpsOf x as %cs ⟨Hcs, -⟩
          ihave %Hlc := ownSlice_len $$ Hcs
          ihave HI : (∃ (j : w64) (c0 : Cmp),
              "i" ∷ i_ptr ↦ j ∗ "c" ∷ c_ptr ↦ c0 ∗
              "ok" ∷ ok_ptr ↦ ((cmpsOfL x).take (sint.nat j)).all (holdsL g.kvs) ∗
              "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z cs.len⌝ : IProp GF) $$ [i c ok]
          · iexists W64 0, _
            rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.all_nil]
            iframe
            ipureintro; word
          wp_for HI
          by_cases Hif : sint.Z j < sint.Z cs.len
          · (try simp only [decide_eq_true Hif, ↓reduceIte]); wp_pures; cleanup_bool_decide
            (try wp_auto); cleanup_bool_decide
            have Hb' : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z cs.len := ⟨Hj.1, Hif⟩
            simp only [Hb', _root_.and_self, ↓reduceIte]
            list_elem (cmpsOfL x) (sint.nat j) as c
            wp_apply wp_load_slice_index cs (sint.Z j) (cmpsOfL x) _ c Hj.1 $$ [Hcs] as Hcs
            · iframe; ipureintro; exact Hc_lookup
            wp_apply wp_holds s.kvs' g.kvs _ c $$ [$Hk] as -
            have Htake : ((cmpsOfL x).take (sint.nat (j + W64 1))).all (holdsL g.kvs) =
                (((cmpsOfL x).take (sint.nat j)).all (holdsL g.kvs) && holdsL g.kvs c) := by
              rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_add_one, Hc_lookup]
              simp [List.all_append]
            cases hh : holdsL g.kvs c
            · try wp_auto
              wp_for_post
              iframe
              iexists j + W64 1, _
              rw [Htake, hh, Bool.and_false]
              iframe
              ipureintro; word
            · try wp_auto
              wp_for_post
              iframe
              iexists j + W64 1, _
              rw [Htake, hh, Bool.and_true]
              iframe
              ipureintro; word
          · (try simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte]); wp_pures
            cleanup_bool_decide; (try wp_auto); cleanup_bool_decide
            have hall : (cmpsOfL x).take (sint.nat j) = cmpsOfL x := List.take_of_length_le (by word)
            rw [hall]
            wp_apply wp_elseOf x as %se ⟨Hse, -⟩
            generalize hok : (cmpsOfL x).all (holdsL g.kvs) = okb
            cases okb
            · try wp_auto
              wp_apply wp_runOps s.kvs' g.kvs (s.rev' + W64 1) se (elseOfL x) _ $$ [$Hk $Hse]
                as %kvs' %res %ch ⟨-, #Hkvs, Hres, -, %Hch⟩
              · ipureintro; have := elseOfL_length x; omega
              wp_if_destruct
              · wp_apply wp_withRes _ _ _ _ $$ [$Hres] as %o' ⟨-, %Ho'⟩
                iapply HΦ
                have e : mstepL x g = (⟨(runOpsL g.kvs (g.rev + W64 1) (elseOfL x)).1, g.rev⟩,
                    withResL { zOut with Rev' := g.rev, Ok' := false } (runOpsL g.kvs (g.rev + W64 1) (elseOfL x)).2.1) := by
                  unfold mstepL; rw [if_neg H0, if_neg H1, if_neg H2, if_neg H3]
                  simp only [cmpsOk, hok, ← Hr, ← Hch, ↓reduceIte, Bool.false_eq_true]
                rw [e, Ho', ← Hr]
                simp only
                isplit
                · isplit
                  · iexact Hkvs
                  · ipureintro; first | rfl | trivial
                · ipureintro; first | rfl | trivial
              · wp_apply wp_withRes _ _ _ _ $$ [$Hres] as %o' ⟨-, %Ho'⟩
                iapply HΦ
                have e : mstepL x g = (⟨(runOpsL g.kvs (g.rev + W64 1) (elseOfL x)).1, g.rev + W64 1⟩,
                    withResL { zOut with Rev' := g.rev + W64 1, Ok' := false } (runOpsL g.kvs (g.rev + W64 1) (elseOfL x)).2.1) := by
                  unfold mstepL; rw [if_neg H0, if_neg H1, if_neg H2, if_neg H3]
                  simp only [cmpsOk, hok, ← Hr, ← Hch, ↓reduceIte, Bool.false_eq_true]
                rw [e, Ho', ← Hr]
                simp only
                isplit
                · isplit
                  · iexact Hkvs
                  · ipureintro; first | rfl | trivial
                · ipureintro; first | rfl | trivial
            · try wp_auto
              wp_apply wp_thenOf x as %st' ⟨Hst, -⟩
              wp_apply wp_runOps s.kvs' g.kvs (s.rev' + W64 1) st' (thenOfL x) _ $$ [$Hk $Hst]
                as %kvs' %res %ch ⟨-, #Hkvs, Hres, -, %Hch⟩
              · ipureintro; have := thenOfL_length x; omega
              wp_if_destruct
              · wp_apply wp_withRes _ _ _ _ $$ [$Hres] as %o' ⟨-, %Ho'⟩
                iapply HΦ
                have e : mstepL x g = (⟨(runOpsL g.kvs (g.rev + W64 1) (thenOfL x)).1, g.rev⟩,
                    withResL { zOut with Rev' := g.rev, Ok' := true } (runOpsL g.kvs (g.rev + W64 1) (thenOfL x)).2.1) := by
                  unfold mstepL; rw [if_neg H0, if_neg H1, if_neg H2, if_neg H3]
                  simp only [cmpsOk, hok, ← Hr, ← Hch, ↓reduceIte, Bool.false_eq_true]
                rw [e, Ho', ← Hr]
                simp only
                isplit
                · isplit
                  · iexact Hkvs
                  · ipureintro; first | rfl | trivial
                · ipureintro; first | rfl | trivial
              · wp_apply wp_withRes _ _ _ _ $$ [$Hres] as %o' ⟨-, %Ho'⟩
                iapply HΦ
                have e : mstepL x g = (⟨(runOpsL g.kvs (g.rev + W64 1) (thenOfL x)).1, g.rev + W64 1⟩,
                    withResL { zOut with Rev' := g.rev + W64 1, Ok' := true } (runOpsL g.kvs (g.rev + W64 1) (thenOfL x)).2.1) := by
                  unfold mstepL; rw [if_neg H0, if_neg H1, if_neg H2, if_neg H3]
                  simp only [cmpsOk, hok, ← Hr, ← Hch, ↓reduceIte, Bool.false_eq_true]
                rw [e, Ho', ← Hr]
                simp only
                isplit
                · isplit
                  · iexact Hkvs
                  · ipureintro; first | rfl | trivial
                · ipureintro; first | rfl | trivial

end proof

end linkvtxn
end EtcdGrove
end Perennial

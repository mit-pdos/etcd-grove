/- Lean-first (no Rocq counterpart). The proof of `openBound`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.openBound
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.nameBound
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RefLemmas

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

theorem openBound.wp_proof (wp_nameBound : nameBound.spec (GF := GF) (hG := hG)) :
    openBound.spec (GF := GF) (hG := hG) := by
  intro s imgs a
  wp_start as #Hr
  iunfold imgsRep at Hr
  icases Hr with ⟨%vs, #Hs, #Hel⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hel_len := imgsElems_length $$ Hel
  wp_auto
  ihave HI : (∃ (i : w64),
      "i" ∷ i_ptr ↦ i ∗
      "best" ∷ best_ptr ↦ (imgs.take (sint.nat i)).foldl
        (fun best i => if uint.nat best < uint.nat (tNameBound i a) then tNameBound i a else best)
        (W64 0) ∗
      "imgs" ∷ imgs_ptr ↦ s ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s.len⌝ : IProp GF) $$ [i best imgs]
  · iexists W64 0
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp only [List.take_zero, List.foldl_nil]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  by_cases hlt : sint.Z i < sint.Z s.len
  · rw [if_pos (by simp [hlt])]
    have hil : sint.nat i < vs.length := by
      have : sint.nat i < sint.nat s.len := by word
      omega
    obtain ⟨v, Hv⟩ : ∃ v, vs[sint.nat i]? = some v := ⟨_, List.getElem?_eq_getElem hil⟩
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := ⟨Hi.1, hlt⟩
    icases ownSlice_elem_acc (sint.Z i) v s DFrac.discard vs Hi.1 (by simpa [sint.nat] using Hv) $$ Hs
      with ⟨Hv, -⟩
    icases imgsElems_lookup vs imgs (sint.nat i) v Hv $$ Hel with ⟨%img, %Himg, #Himgr⟩
    wp_auto
    repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
    wp_apply wp_nameBound
    · iexact Himgr
    iintro -
    wp_auto
    have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    have hstep := foldl_take_succ
      (fun best i => if uint.nat best < uint.nat (tNameBound i a) then tNameBound i a else best)
      (W64 0) imgs (sint.nat i) img Himg
    wp_if_destruct
    · wp_for_post
      iframe
      iexists i + W64 1
      rw [hi1, hstep, if_pos (by word)]
      iframe
      ipureintro; constructor <;> word
    · wp_for_post
      iframe
      iexists i + W64 1
      rw [hi1, hstep, if_neg (by word)]
      iframe
      ipureintro; constructor <;> word
  · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hin : sint.nat i = imgs.length := by
      have : sint.nat i = sint.nat s.len := by word
      omega
    wp_auto
    rw [hin, List.take_length]
    rw [show List.foldl (fun best i => if uint.nat best < uint.nat (tNameBound i a) then tNameBound i a else best) (W64 0) imgs = tOpenBound imgs a from rfl]
    iapply HΦ
    itrivial

end proof

end etcd_wal
end EtcdGrove
end Perennial

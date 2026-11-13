/- Lean-first (no Rocq counterpart). The proof of `cutPos`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.cutPos
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.hsEmpty

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

theorem cutPos.wp_proof (wp_hsEmpty : hsEmpty.spec (GF := GF) (hG := hG)) :
    cutPos.spec (GF := GF) (hG := hG) := by
  intro s h b hb0 hb
  wp_start as #Hr
  iunfold opsRep at Hr
  icases Hr with ⟨%es, #Hs, #Hel⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hel_len := opsElems_length $$ Hel
  ihave HΦ := ret_gen _ _ _ $$ HΦ
  wp_auto
  wp_if_destruct
  · iapply HΦ
    isplitl []
    · ipureintro; rw [eq_comm, show sint.nat (W64 0) = 0 from rfl]; simp [tCutPos]
    · itrivial
  · have hb1 : sint.nat (b - W64 1) = sint.nat b - 1 := by
      have : b ≠ W64 0 := Hif
      word
    have hil : sint.nat b - 1 < es.length := by
      have : sint.nat b ≠ 0 := by intro h0; apply Hif; word
      omega
    obtain ⟨v, Hv⟩ : ∃ v, es[sint.nat b - 1]? = some v := ⟨_, List.getElem?_eq_getElem hil⟩
    have hbb : 0 ≤ sint.Z (b - W64 1) ∧ sint.Z (b - W64 1) < sint.Z s.len := by
      constructor <;> word
    simp only [hbb, _root_.and_self, ↓reduceIte]
    icases ownSlice_elem_acc (sint.Z (b - W64 1)) v s DFrac.discard es hbb.1
      (by rw [show (sint.Z (b - W64 1)).toNat = sint.nat b - 1 by word]; exact Hv) $$ Hs with ⟨Hv, -⟩
    icases opsElems_lookup es h (sint.nat b - 1) v Hv $$ Hel with ⟨%op, %Hop, #Hopr⟩
    iunfold opRep at Hopr
    icases Hopr with ⟨%Hf, #Hoe⟩
    obtain ⟨hsn, hhs, -, -⟩ := Hf
    ihave %Hoel := ownSlice_len $$ Hoe
    have hb0' : sint.nat b ≠ 0 := by intro h0; apply Hif; word
    have htc : tCutPos h (sint.nat b) = (!op.snap && !(tHsEmpty op.hs && op.ents.isEmpty)) := by
      simp only [tCutPos, hb0', decide_false, Bool.false_or, Hop]
    wp_auto
    rw [hsn]
    cases hos : op.snap
    · wp_auto
      wp_apply wp_hsEmpty
      rw [hhs]
      cases he : tHsEmpty op.hs
      · wp_auto
        iapply HΦ
        isplitl []
        · ipureintro; rw [htc, hos, he]; rfl
        · itrivial
      · wp_auto
        iapply HΦ
        isplitl []
        · ipureintro; rw [htc, hos, he]
          have hz : (v.ents'.len = W64 0) ↔ op.ents.isEmpty = true := by
            rw [List.isEmpty_iff, ← List.length_eq_zero_iff, Hoel.1]
            constructor <;> intro h0 <;> word
          by_cases hz' : v.ents'.len = W64 0
          · simp [hz', hz.1 hz']
          · have : op.ents.isEmpty = false := by
              cases hh : op.ents.isEmpty
              · rfl
              · exact absurd (hz.2 hh) hz'
            simp [this]; exact hz'
        · itrivial
    · wp_auto
      iapply HΦ
      isplitl []
      · ipureintro; rw [htc, hos]; rfl
      · itrivial

end proof

end etcd_wal
end EtcdGrove
end Perennial

/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Trace__StepLine`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__StepLine
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__Next
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.indexOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Violated

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

set_option maxHeartbeats 2000000 in
theorem Trace.StepLine.wp_proof
    (wp_Next : Trace.Next.spec (GF := GF) (hG := hG))
    (wp_indexOf : indexOf.spec (GF := GF) (hG := hG))
    (wp_Violated : State.Violated.spec (GF := GF) (hG := hG)) :
    Trace.StepLine.spec (GF := GF) (hG := hG) := by
  intro t tr g ts invariants
  wp_start as ⟨#Ht, #Hts, %Hok, %Hnoerr⟩
  obtain ⟨Hok1, Hok2⟩ := Hok
  open_trace
  have hlenb := Hv.len_lt
  wp_auto
  wp_apply wp_slice_literal [g]
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨Hfr, Hfrc⟩
  try wp_auto
  wp_apply wp_slice_literal [g]
  isplitr
  · ipureintro; rfl
  iintro %vsl ⟨Hvi, Hvic⟩
  try wp_auto
  ihave Hou : (zero_val GoSlice : GoSlice) ↦* ([] : List G.TState) $$ []
  · iapply ownSlice_nil
  ihave Houc : ownSliceCap G.TState (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (fsl vsl osl : GoSlice) (gfr gvi gou : List G.TState) (fr vi ou : List TState)
      (info : StepInfo) (gi : G.StepInfo),
      "frontier" ∷ frontier_ptr ↦ fsl ∗ "Hfr" ∷ fsl ↦* gfr ∗ "Hfrc" ∷ ownSliceCap G.TState fsl (DFrac.own 1) ∗
      "Hfrl" ∷ ([∗list] h;x ∈ gfr;fr, tstateRO (GF := GF) h x) ∗
      "visited" ∷ visited_ptr ↦ vsl ∗ "Hvi" ∷ vsl ↦* gvi ∗ "Hvic" ∷ ownSliceCap G.TState vsl (DFrac.own 1) ∗
      "Hvil" ∷ ([∗list] h;x ∈ gvi;vi, tstateRO (GF := GF) h x) ∗
      "out" ∷ out_ptr ↦ osl ∗ "Hou" ∷ osl ↦* gou ∗ "Houc" ∷ ownSliceCap G.TState osl (DFrac.own 1) ∗
      "Houl" ∷ ([∗list] h;x ∈ gou;ou, tstateRO (GF := GF) h x) ∗
      "info" ∷ info_ptr ↦ gi ∗
      "%Hinv" ∷ ⌜info.violation = none ∧ gi.Branched' = info.branched ∧ strRel gi.Violation' "" ∧
        (∀ r, tr.StepLoop ts.l invariants fr (ou, vi, info) r → tr.StepLineRel ts invariants r) ∧
        (∀ f ∈ fr, tr.LineReach ts f)⌝) $$ [frontier Hfr Hfrc visited Hvi Hvic out Hou Houc info]
  · iexists _, _, _, _, _, _, [ts], [ts], [], {}, _
    isplitl [frontier]
    · iexact frontier
    isplitl [Hfr]
    · iexact Hfr
    isplitl [Hfrc]
    · iexact Hfrc
    isplitr
    · iapply BigSepL2.bigSepL2_cons.2; isplitr; iexact Hts; iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    isplitl [visited]
    · iexact visited
    isplitl [Hvi]
    · iexact Hvi
    isplitl [Hvic]
    · iexact Hvic
    isplitr
    · iapply BigSepL2.bigSepL2_cons.2; isplitr; iexact Hts; iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    isplitl [out]
    · iexact out
    isplitl [Hou]
    · iexact Hou
    isplitl [Houc]
    · iexact Houc
    isplitr
    · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    isplitl [info]
    · iexact info
    ipureintro
    refine ⟨rfl, rfl, strRel_empty, fun r h => h, ?_⟩
    intro f hf; simp at hf; subst hf; exact .start
  wp_for IH
  obtain ⟨hvn, hbr, hvs, hcomp, hreach⟩ := Hinv
  ihave %Hfrl0 := BigSepL2.bigSepL2_length $$ Hfrl
  ihave %Hfrsl := ownSlice_len $$ Hfr
  wp_if_destruct
  · -- a round over the frontier
    have hfrne : fr ≠ [] := by
      intro h; subst h
      have h1 : (gfr.length : Int) = sint.Z fsl.len := by rw [Hfrsl.1]; word
      rw [Hfrl0] at h1; simp at h1; rw [← h1] at Hif; exact absurd Hif (by decide)
    obtain ⟨R, hR⟩ : ∃ R, tr.stepRound ts.l invariants fr (ou, vi, info) = .ok R := by
      cases h : tr.stepRound ts.l invariants fr (ou, vi, info) with
      | error e => exact absurd (hcomp _ (Trace.StepLoop.error _ _ e hfrne h)) (Hnoerr e)
      | ok R => exact ⟨R, rfl⟩
    have hR' := hR
    rw [Trace.stepRound_eq] at hR'
    icases Hfrl with #Hfrl
    ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List G.TState) $$ []
    · iapply ownSlice_nil
    ihave Hnilc : ownSliceCap G.TState (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
    · iapply ownSliceCap_nil
    ihave IHr : iprop(∃ (k : w64) (fv : G.TState) (nsl vsl2 osl2 : GoSlice) (gnx gvi2 gou2 : List G.TState)
        (ou2 vi2 nx2 : List TState) (info2 : StepInfo) (gi2 : G.StepInfo),
        "i" ∷ i_ptr ↦ k ∗ "f" ∷ f_ptr ↦ fv ∗ "Hfr" ∷ fsl ↦* gfr ∗
        "next" ∷ next_ptr ↦ nsl ∗ "Hnx" ∷ nsl ↦* gnx ∗ "Hnxc" ∷ ownSliceCap G.TState nsl (DFrac.own 1) ∗
        "Hnxl" ∷ ([∗list] h;x ∈ gnx;nx2, tstateRO (GF := GF) h x) ∗
        "visited" ∷ visited_ptr ↦ vsl2 ∗ "Hvi" ∷ vsl2 ↦* gvi2 ∗ "Hvic" ∷ ownSliceCap G.TState vsl2 (DFrac.own 1) ∗
        "Hvil" ∷ ([∗list] h;x ∈ gvi2;vi2, tstateRO (GF := GF) h x) ∗
        "out" ∷ out_ptr ↦ osl2 ∗ "Hou" ∷ osl2 ↦* gou2 ∗ "Houc" ∷ ownSliceCap G.TState osl2 (DFrac.own 1) ∗
        "Houl" ∷ ([∗list] h;x ∈ gou2;ou2, tstateRO (GF := GF) h x) ∗
        "info" ∷ info_ptr ↦ gi2 ∗
        "%Hr" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z fsl.len ∧
          (fr.take (sint.nat k)).foldlM (tr.stepOuterF ts.l invariants) (ou, vi, [], info) =
            .ok (ou2, vi2, nx2, info2) ∧
          info2.violation = none ∧ gi2.Branched' = info2.branched ∧ strRel gi2.Violation' "" ∧
          (∀ s ∈ nx2, tr.LineReach ts s)⌝)
        $$ [i f Hfr next Hnil Hnilc visited Hvi Hvic Hvil out Hou Houc Houl info]
    · iexists _, _, _, vsl, osl, [], gvi, gou, ou, vi, [], info, gi
      iframe
      isplitr
      · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl, hvn, hbr, hvs, by simp⟩
    wp_for IHr
    obtain ⟨hk0, hk1, hacc, hvn2, hbr2, hvs2, hnx2⟩ := Hr
    wp_if_destruct
    · have Hlt : sint.nat k < gfr.length := by clear hacc; rw [Hfrsl.1]; word
      obtain ⟨gx, Hgx⟩ : ∃ gx, gfr[sint.nat k]? = some gx := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨x, Hx⟩ : ∃ x, fr[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem (Hfrl0 ▸ Hlt)⟩
      ihave #Hgxx := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => tstateRO (GF := GF) a b) Hgx Hx $$ Hfrl
      have hk1' : sint.nat (k + W64 1) = sint.nat k + 1 := by clear hacc; word
      have hxr : tr.LineReach ts x := hreach x (List.mem_of_getElem? Hx)
      obtain ⟨a', hstep, htake⟩ := foldlM_ok_step _ _ _ _ _ _ _ hR' hacc Hx
      obtain ⟨succ, hnext, r5, hinner, ha'⟩ := Trace.stepOuterF_ok _ _ _ _ _ _ _ _ _ hvn2 hstep
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z fsl.len from ⟨hk0, Hif⟩))]
      wp_apply wp_load_slice_index _ (sint.Z k) gfr (DFrac.own 1) gx hk0 $$ [Hfr] as Hfr
      · iframe Hfr; ipureintro; exact Hgx
      try wp_auto
      wp_apply wp_Next t tr gx x succ $$ [Ht Hgxx] as %ssl Hss
      · iframe Ht Hgxx; ipureintro; exact ⟨Hok1 x hxr, hnext⟩
      iunfold tstatesOut at Hss
      icases Hss with ⟨%gsucc, Hsucc, -, #Hsuccl⟩
      ihave %Hsuccsl := ownSlice_len $$ Hsucc
      ihave %Hsuccl0 := BigSepL2.bigSepL2_length $$ Hsuccl
      try wp_auto
      ihave Hnil2 : (zero_val GoSlice : GoSlice) ↦* ([] : List G.TState) $$ []
      · iapply ownSlice_nil
      ihave Hnilc2 : ownSliceCap G.TState (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
      · iapply ownSliceCap_nil
      ihave IHs : iprop(∃ (m : w64) (sv : G.TState) (fsl3 nsl3 vsl3 osl3 : GoSlice)
          (gfs3 gnx3 gvi3 gou3 : List G.TState) (ou3 vi3 nx3 fr3 : List TState) (info3 : StepInfo) (gi3 : G.StepInfo),
          "i" ∷ i_ptr ↦ m ∗ "s2" ∷ s2_ptr ↦ sv ∗ "Hsucc" ∷ ssl ↦* gsucc ∗
          "fresh" ∷ fresh_ptr ↦ fsl3 ∗ "Hfs" ∷ fsl3 ↦* gfs3 ∗ "Hfsc" ∷ ownSliceCap G.TState fsl3 (DFrac.own 1) ∗
          "Hfsl" ∷ ([∗list] h;x ∈ gfs3;fr3, tstateRO (GF := GF) h x) ∗
          "next" ∷ next_ptr ↦ nsl3 ∗ "Hnx" ∷ nsl3 ↦* gnx3 ∗ "Hnxc" ∷ ownSliceCap G.TState nsl3 (DFrac.own 1) ∗
          "Hnxl" ∷ ([∗list] h;x ∈ gnx3;nx3, tstateRO (GF := GF) h x) ∗
          "visited" ∷ visited_ptr ↦ vsl3 ∗ "Hvi" ∷ vsl3 ↦* gvi3 ∗ "Hvic" ∷ ownSliceCap G.TState vsl3 (DFrac.own 1) ∗
          "Hvil" ∷ ([∗list] h;x ∈ gvi3;vi3, tstateRO (GF := GF) h x) ∗
          "out" ∷ out_ptr ↦ osl3 ∗ "Hou" ∷ osl3 ↦* gou3 ∗ "Houc" ∷ ownSliceCap G.TState osl3 (DFrac.own 1) ∗
          "Houl" ∷ ([∗list] h;x ∈ gou3;ou3, tstateRO (GF := GF) h x) ∗
          "info" ∷ info_ptr ↦ gi3 ∗
          "%Hs" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z ssl.len ∧
            (succ.take (sint.nat m)).foldlM (Trace.stepInnerF ts.l invariants) (ou2, vi2, nx2, [], info2) =
              .ok (ou3, vi3, nx3, fr3, info3) ∧
            info3.violation = none ∧ gi3.Branched' = info3.branched ∧ strRel gi3.Violation' "" ∧
            (∀ s ∈ nx3, tr.LineReach ts s)⌝)
          $$ [i s2 Hsucc fresh Hnil2 Hnilc2 next Hnx Hnxc Hnxl visited Hvi Hvic Hvil out Hou Houc Houl info]
      · iexists _, _, _, nsl, vsl2, osl2, [], gnx, gvi2, gou2, ou2, vi2, nx2, [], info2, gi2
        iframe
        isplitr
        · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
        ipureintro
        refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl, hvn2, hbr2, hvs2, hnx2⟩
      wp_for IHs
      obtain ⟨hm0, hm1, hacc3, hvn3, hbr3, hvs3, hnx3⟩ := Hs
      wp_if_destruct
      · have Hlt2 : sint.nat m < gsucc.length := by clear hacc3; rw [Hsuccsl.1]; word
        obtain ⟨gy, Hgy⟩ : ∃ gy, gsucc[sint.nat m]? = some gy := ⟨_, List.getElem?_eq_getElem Hlt2⟩
        obtain ⟨y, Hy⟩ : ∃ y, succ[sint.nat m]? = some y := ⟨_, List.getElem?_eq_getElem (Hsuccl0 ▸ Hlt2)⟩
        ihave #Hgyy := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => tstateRO (GF := GF) a b) Hgy Hy $$ Hsuccl
        have hm1' : sint.nat (m + W64 1) = sint.nat m + 1 := by clear hacc3; word
        have hyin : y ∈ succ := List.mem_of_getElem? Hy
        obtain ⟨a'', hstep2, htake2⟩ := foldlM_ok_step _ _ _ _ _ _ _ hinner hacc3 Hy
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z ssl.len from ⟨hm0, Hif⟩))]
        wp_apply wp_load_slice_index _ (sint.Z m) gsucc (DFrac.own 1) gy hm0 $$ [Hsucc] as Hsucc
        · iframe Hsucc; ipureintro; exact Hgy
        try wp_auto
        ihave #Hgyy0 := Hgyy
        iunfold tstateRO at Hgyy0
        icases Hgyy0 with ⟨#Hys, %Hyl⟩
        ihave #Hts0 := Hts
        iunfold tstateRO at Hts0
        icases Hts0 with ⟨-, %Htsl⟩
        have hdec : decide (gy.L' = g.L' + W64 1) = decide (y.l = ts.l + 1) := by
          apply decide_eq_decide.2
          constructor
          · intro h
            have h1 : sint.Z gy.L' = sint.Z (g.L' + W64 1) := by rw [h]
            have : sint.Z (g.L' + W64 1) = sint.Z g.L' + 1 := by
              have := Hyl.1; have := Htsl.1; word
            omega
          · intro h
            have h1 : sint.Z gy.L' = sint.Z g.L' + 1 := by omega
            apply (int_eq_iff _ _).2
            have : sint.Z gy.L' < 2 ^ 63 := by word
            rw [h1]; word
        rw [hdec]
        by_cases hyl : y.l = ts.l + 1
        · rw [decide_eq_true hyl]
          wp_auto
          icases Houl with #Houl
          wp_apply wp_indexOf osl3 (DFrac.own 1) gou3 ou3 gy y $$ [Hou Houl Hgyy] as %ko ⟨Hou, %Hko⟩
          · iframe Hou Houl Hgyy
          try wp_auto
          cases hfi : ou3.findIdx? (fun us => us.eq y) with
          | some j =>
            rw [hfi] at Hko
            simp only at Hko
            rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z ko by rw [Hko]; have : sint.Z (W64 0) = 0 := rfl; omega)]
            rw [Trace.stepInnerF_dup_out ts.l invariants ou3 vi3 nx3 fr3 info3 y hvn3 hyl (memEq_of_findIdx?_some hfi)]
              at hstep2
            cases hstep2
            try wp_auto
            wp_for_post
            iframe
            iexists _, _, fsl3, nsl3, vsl3, osl3, gfs3, gnx3, gvi3, gou3, ou3, vi3, nx3, fr3, info3, gi3
            iframe
            try iframe Houl
            try iframe Hvil
            try iframe Hnxl
            try iframe Hfsl
            try iframe Houl'
            try iframe Hvil'
            try iframe Hnxl'
            try iframe Hfsl'
            ipureintro
            refine ⟨by clear hacc3 htake2; word, by clear hacc3 htake2; word, by rw [hm1', htake2], hvn3, hbr3, hvs3, hnx3⟩
          | none =>
            rw [hfi] at Hko
            simp only at Hko
            rw [decide_eq_false (show ¬ sint.Z (W64 0) ≤ sint.Z ko by rw [Hko]; have : sint.Z (W64 0) = 0 := rfl; omega)]
            rw [Trace.stepInnerF_new_out ts.l invariants ou3 vi3 nx3 fr3 info3 y hvn3 hyl (memEq_of_findIdx?_none hfi)]
              at hstep2
            try wp_auto
            wp_apply wp_slice_literal [gy]
            isplitr
            · ipureintro; rfl
            iintro %slo ⟨Hslo, -⟩
            try wp_auto
            wp_apply wp_slice_append $$ [Hou Houc Hslo] as %osl4 ⟨Hou, Houc, -⟩
            · iframe
            try wp_auto
            ihave #Houl' : ([∗list] h;x ∈ gou3 ++ [gy];ou3 ++ [y], tstateRO (GF := GF) h x) $$ []
            · iapply BigSepL2.bigSepL2_snoc.2
              iframe Houl Hgyy
            iclear Houl
            have hnxN : ∀ s ∈ nx3, tr.LineReach ts s := hnx3
            obtain ⟨i', hni, ha''⟩ := except_bind_pure_ok _ _ _ hstep2
            icases Hfsl with #Hfsl
            wp_apply wp_indexOf fsl3 (DFrac.own 1) gfs3 fr3 gy y $$ [Hfs Hfsl Hgyy] as %kf ⟨Hfs, %Hkf⟩
            · iframe Hfs Hfsl Hgyy
            try wp_auto
            cases hff : fr3.findIdx? (fun us => us.eq y) with
            | some j =>
              rw [hff] at Hkf
              simp only at Hkf
              rw [decide_eq_false (show ¬ sint.Z kf < sint.Z (W64 0) by rw [Hkf]; have : sint.Z (W64 0) = 0 := rfl; omega)]
              have hmf := memEq_of_findIdx?_some hff
              simp only [hmf, ↓reduceIte] at ha''
              try wp_auto
              cases invariants
              · rw [Trace.stepNewInfo_false] at hni
                cases hni
                try simp only at ha''
                try wp_auto
                wp_for_post
                iframe
                iexists _, _, fsl3, nsl3, vsl3, osl4, gfs3, gnx3, gvi3, (gou3 ++ [gy]), (ou3 ++ [y]), vi3, nx3, fr3, info3, gi3
                iframe
                try iframe Houl
                try iframe Hvil
                try iframe Hnxl
                try iframe Hfsl
                try iframe Houl'
                try iframe Hvil'
                try iframe Hnxl'
                try iframe Hfsl'
                ipureintro
                refine ⟨by clear hacc3 htake2; word, by clear hacc3 htake2; word, by rw [hm1', htake2, ha''], hvn3, hbr3, hvs3, hnxN⟩
              · cases hv : y.s.violated with
                | error e => simp [Trace.stepNewInfo, hv, Bind.bind, Except.bind] at hni
                | ok r =>
                rw [Trace.stepNewInfo_true _ _ _ hv] at hni
                cases hni
                try simp only at ha''
                try wp_auto
                wp_apply wp_Violated gy.S' y.s r $$ [Hys] as %vgo %Hvgo
                · iframe Hys; ipureintro
                  have hvo := Hok2 rfl x succ y hxr hnext hyin
                  exact ⟨hvo.1, hvo.2, hv⟩
                cases r with
                | none =>
                  have hv0 : vgo = go!"" := (strRel_eq_iff Hvgo strRel_empty).2 rfl
                  subst hv0
                  try wp_auto
                  wp_for_post
                  iframe
                  iexists _, _, fsl3, nsl3, vsl3, osl4, gfs3, gnx3, gvi3, (gou3 ++ [gy]), (ou3 ++ [y]), vi3, nx3, fr3, info3, gi3
                  iframe
                  try iframe Houl
                  try iframe Hvil
                  try iframe Hnxl
                  try iframe Hfsl
                  try iframe Houl'
                  try iframe Hvil'
                  try iframe Hnxl'
                  try iframe Hfsl'
                  ipureintro
                  refine ⟨by clear hacc3 htake2; word, by clear hacc3 htake2; word, by rw [hm1', htake2, ha''], hvn3, hbr3, hvs3, hnxN⟩
                | some w =>
                  have hw := State.violated_some_ne hv
                  have hv0 : vgo ≠ go!"" := fun h => hw ((strRel_eq_iff Hvgo strRel_empty).1 h)
                  rw [decide_eq_false hv0]
                  try wp_auto
                  -- the violation ends the search: the rest of the round skips
                  have hr5 : r5 = a'' := foldlM_take_fix _ _ _ _ _ _ hinner htake2 (fun l' =>
                    Trace.stepInnerF_foldlM_skip _ _ l' a'' (by rw [ha'']; rfl))
                  have hR2 : R = a' := foldlM_take_fix _ _ _ _ _ _ hR' htake (fun l' =>
                    Trace.stepOuterF_foldlM_skip _ _ _ l' a' (by rw [ha', hr5, ha'']; rfl))
                  have hrel := hcomp _ (Trace.StepLoop.violation fr (ou, vi, info) R.1 R.2.1 R.2.2.1 R.2.2.2 hfrne
                    (by rw [hR]) (by rw [hR2, ha', hr5, ha'']; rfl))
                  rw [hR2, ha', hr5, ha''] at hrel
                  simp only at hrel
                  wp_for_post
                  try wp_auto
                  wp_for_post
                  try wp_auto
                  wp_for_post
                  try wp_auto
                  iapply HΦ
                  iexists (ou3 ++ [y]), { info3 with violation := some w }
                  isplitr
                  · ipureintro
                    refine ⟨hrel, hbr3, ?_⟩
                    exact Hvgo
                  iunfold tstatesOut
                  iexists (gou3 ++ [gy])
                  iframe
                  try iexact Houl'
            | none =>
              rw [hff] at Hkf
              simp only at Hkf
              rw [decide_eq_true (show sint.Z kf < sint.Z (W64 0) by rw [Hkf]; have : sint.Z (W64 0) = 0 := rfl; omega)]
              have hmf := memEq_of_findIdx?_none hff
              simp only [hmf, Bool.false_eq_true, ↓reduceIte] at ha''
              try wp_auto
              wp_apply wp_slice_literal [gy]
              isplitr
              · ipureintro; rfl
              iintro %slf ⟨Hslf, -⟩
              try wp_auto
              wp_apply wp_slice_append $$ [Hfs Hfsc Hslf] as %fsl4 ⟨Hfs, Hfsc, -⟩
              · iframe
              try wp_auto
              ihave #Hfsl' : ([∗list] h;x ∈ gfs3 ++ [gy];fr3 ++ [y], tstateRO (GF := GF) h x) $$ []
              · iapply BigSepL2.bigSepL2_snoc.2
                iframe Hfsl Hgyy
              iclear Hfsl
              cases invariants
              · rw [Trace.stepNewInfo_false] at hni
                cases hni
                try simp only at ha''
                try wp_auto
                wp_for_post
                iframe
                iexists _, _, fsl4, nsl3, vsl3, osl4, (gfs3 ++ [gy]), gnx3, gvi3, (gou3 ++ [gy]), (ou3 ++ [y]), vi3, nx3, (fr3 ++ [y]), info3, gi3
                iframe
                try iframe Houl
                try iframe Hvil
                try iframe Hnxl
                try iframe Hfsl
                try iframe Houl'
                try iframe Hvil'
                try iframe Hnxl'
                try iframe Hfsl'
                ipureintro
                refine ⟨by clear hacc3 htake2; word, by clear hacc3 htake2; word, by rw [hm1', htake2, ha''], hvn3, hbr3, hvs3, hnxN⟩
              · cases hv : y.s.violated with
                | error e => simp [Trace.stepNewInfo, hv, Bind.bind, Except.bind] at hni
                | ok r =>
                rw [Trace.stepNewInfo_true _ _ _ hv] at hni
                cases hni
                try simp only at ha''
                try wp_auto
                wp_apply wp_Violated gy.S' y.s r $$ [Hys] as %vgo %Hvgo
                · iframe Hys; ipureintro
                  have hvo := Hok2 rfl x succ y hxr hnext hyin
                  exact ⟨hvo.1, hvo.2, hv⟩
                cases r with
                | none =>
                  have hv0 : vgo = go!"" := (strRel_eq_iff Hvgo strRel_empty).2 rfl
                  subst hv0
                  try wp_auto
                  wp_for_post
                  iframe
                  iexists _, _, fsl4, nsl3, vsl3, osl4, (gfs3 ++ [gy]), gnx3, gvi3, (gou3 ++ [gy]), (ou3 ++ [y]), vi3, nx3, (fr3 ++ [y]), info3, gi3
                  iframe
                  try iframe Houl
                  try iframe Hvil
                  try iframe Hnxl
                  try iframe Hfsl
                  try iframe Houl'
                  try iframe Hvil'
                  try iframe Hnxl'
                  try iframe Hfsl'
                  ipureintro
                  refine ⟨by clear hacc3 htake2; word, by clear hacc3 htake2; word, by rw [hm1', htake2, ha''], hvn3, hbr3, hvs3, hnxN⟩
                | some w =>
                  have hw := State.violated_some_ne hv
                  have hv0 : vgo ≠ go!"" := fun h => hw ((strRel_eq_iff Hvgo strRel_empty).1 h)
                  rw [decide_eq_false hv0]
                  try wp_auto
                  -- the violation ends the search: the rest of the round skips
                  have hr5 : r5 = a'' := foldlM_take_fix _ _ _ _ _ _ hinner htake2 (fun l' =>
                    Trace.stepInnerF_foldlM_skip _ _ l' a'' (by rw [ha'']; rfl))
                  have hR2 : R = a' := foldlM_take_fix _ _ _ _ _ _ hR' htake (fun l' =>
                    Trace.stepOuterF_foldlM_skip _ _ _ l' a' (by rw [ha', hr5, ha'']; rfl))
                  have hrel := hcomp _ (Trace.StepLoop.violation fr (ou, vi, info) R.1 R.2.1 R.2.2.1 R.2.2.2 hfrne
                    (by rw [hR]) (by rw [hR2, ha', hr5, ha'']; rfl))
                  rw [hR2, ha', hr5, ha''] at hrel
                  simp only at hrel
                  wp_for_post
                  try wp_auto
                  wp_for_post
                  try wp_auto
                  wp_for_post
                  try wp_auto
                  iapply HΦ
                  iexists (ou3 ++ [y]), { info3 with violation := some w }
                  isplitr
                  · ipureintro
                    refine ⟨hrel, hbr3, ?_⟩
                    exact Hvgo
                  iunfold tstatesOut
                  iexists (gou3 ++ [gy])
                  iframe
                  try iexact Houl'
        · rw [decide_eq_false hyl]
          wp_auto
          icases Hvil with #Hvil
          wp_apply wp_indexOf vsl3 (DFrac.own 1) gvi3 vi3 gy y $$ [Hvi Hvil Hgyy] as %ko ⟨Hvi, %Hko⟩
          · iframe Hvi Hvil Hgyy
          try wp_auto
          cases hfi : vi3.findIdx? (fun us => us.eq y) with
          | some j =>
            rw [hfi] at Hko
            simp only at Hko
            rw [decide_eq_true (show sint.Z (W64 0) ≤ sint.Z ko by rw [Hko]; have : sint.Z (W64 0) = 0 := rfl; omega)]
            rw [Trace.stepInnerF_dup_vis ts.l invariants ou3 vi3 nx3 fr3 info3 y hvn3 hyl (memEq_of_findIdx?_some hfi)]
              at hstep2
            cases hstep2
            try wp_auto
            wp_for_post
            iframe
            iexists _, _, fsl3, nsl3, vsl3, osl3, gfs3, gnx3, gvi3, gou3, ou3, vi3, nx3, fr3, info3, gi3
            iframe
            try iframe Houl
            try iframe Hvil
            try iframe Hnxl
            try iframe Hfsl
            try iframe Houl'
            try iframe Hvil'
            try iframe Hnxl'
            try iframe Hfsl'
            ipureintro
            refine ⟨by clear hacc3 htake2; word, by clear hacc3 htake2; word, by rw [hm1', htake2], hvn3, hbr3, hvs3, hnx3⟩
          | none =>
            rw [hfi] at Hko
            simp only at Hko
            rw [decide_eq_false (show ¬ sint.Z (W64 0) ≤ sint.Z ko by rw [Hko]; have : sint.Z (W64 0) = 0 := rfl; omega)]
            rw [Trace.stepInnerF_new_vis ts.l invariants ou3 vi3 nx3 fr3 info3 y hvn3 hyl (memEq_of_findIdx?_none hfi)]
              at hstep2
            try wp_auto
            wp_apply wp_slice_literal [gy]
            isplitr
            · ipureintro; rfl
            iintro %slv ⟨Hslv, -⟩
            try wp_auto
            wp_apply wp_slice_append $$ [Hvi Hvic Hslv] as %vsl4 ⟨Hvi, Hvic, -⟩
            · iframe
            try wp_auto
            wp_apply wp_slice_literal [gy]
            isplitr
            · ipureintro; rfl
            iintro %sln ⟨Hsln, -⟩
            try wp_auto
            wp_apply wp_slice_append $$ [Hnx Hnxc Hsln] as %nsl4 ⟨Hnx, Hnxc, -⟩
            · iframe
            try wp_auto
            ihave #Hvil' : ([∗list] h;x ∈ gvi3 ++ [gy];vi3 ++ [y], tstateRO (GF := GF) h x) $$ []
            · iapply BigSepL2.bigSepL2_snoc.2
              iframe Hvil Hgyy
            iclear Hvil
            icases Hnxl with #Hnxl
            ihave #Hnxl' : ([∗list] h;x ∈ gnx3 ++ [gy];nx3 ++ [y], tstateRO (GF := GF) h x) $$ []
            · iapply BigSepL2.bigSepL2_snoc.2
              iframe Hnxl Hgyy
            iclear Hnxl
            have hnxN : ∀ s ∈ nx3 ++ [y], tr.LineReach ts s := by
              intro s hs
              rcases List.mem_append.1 hs with hs | hs
              · exact hnx3 s hs
              · rw [List.mem_singleton] at hs; rw [hs]; exact .step x succ y hxr hnext hyin hyl
            obtain ⟨i', hni, ha''⟩ := except_bind_pure_ok _ _ _ hstep2
            icases Hfsl with #Hfsl
            wp_apply wp_indexOf fsl3 (DFrac.own 1) gfs3 fr3 gy y $$ [Hfs Hfsl Hgyy] as %kf ⟨Hfs, %Hkf⟩
            · iframe Hfs Hfsl Hgyy
            try wp_auto
            cases hff : fr3.findIdx? (fun us => us.eq y) with
            | some j =>
              rw [hff] at Hkf
              simp only at Hkf
              rw [decide_eq_false (show ¬ sint.Z kf < sint.Z (W64 0) by rw [Hkf]; have : sint.Z (W64 0) = 0 := rfl; omega)]
              have hmf := memEq_of_findIdx?_some hff
              simp only [hmf, ↓reduceIte] at ha''
              try wp_auto
              cases invariants
              · rw [Trace.stepNewInfo_false] at hni
                cases hni
                try simp only at ha''
                try wp_auto
                wp_for_post
                iframe
                iexists _, _, fsl3, nsl4, vsl4, osl3, gfs3, (gnx3 ++ [gy]), (gvi3 ++ [gy]), gou3, ou3, (vi3 ++ [y]), (nx3 ++ [y]), fr3, info3, gi3
                iframe
                try iframe Houl
                try iframe Hvil
                try iframe Hnxl
                try iframe Hfsl
                try iframe Houl'
                try iframe Hvil'
                try iframe Hnxl'
                try iframe Hfsl'
                ipureintro
                refine ⟨by clear hacc3 htake2; word, by clear hacc3 htake2; word, by rw [hm1', htake2, ha''], hvn3, hbr3, hvs3, hnxN⟩
              · cases hv : y.s.violated with
                | error e => simp [Trace.stepNewInfo, hv, Bind.bind, Except.bind] at hni
                | ok r =>
                rw [Trace.stepNewInfo_true _ _ _ hv] at hni
                cases hni
                try simp only at ha''
                try wp_auto
                wp_apply wp_Violated gy.S' y.s r $$ [Hys] as %vgo %Hvgo
                · iframe Hys; ipureintro
                  have hvo := Hok2 rfl x succ y hxr hnext hyin
                  exact ⟨hvo.1, hvo.2, hv⟩
                cases r with
                | none =>
                  have hv0 : vgo = go!"" := (strRel_eq_iff Hvgo strRel_empty).2 rfl
                  subst hv0
                  try wp_auto
                  wp_for_post
                  iframe
                  iexists _, _, fsl3, nsl4, vsl4, osl3, gfs3, (gnx3 ++ [gy]), (gvi3 ++ [gy]), gou3, ou3, (vi3 ++ [y]), (nx3 ++ [y]), fr3, info3, gi3
                  iframe
                  try iframe Houl
                  try iframe Hvil
                  try iframe Hnxl
                  try iframe Hfsl
                  try iframe Houl'
                  try iframe Hvil'
                  try iframe Hnxl'
                  try iframe Hfsl'
                  ipureintro
                  refine ⟨by clear hacc3 htake2; word, by clear hacc3 htake2; word, by rw [hm1', htake2, ha''], hvn3, hbr3, hvs3, hnxN⟩
                | some w =>
                  have hw := State.violated_some_ne hv
                  have hv0 : vgo ≠ go!"" := fun h => hw ((strRel_eq_iff Hvgo strRel_empty).1 h)
                  rw [decide_eq_false hv0]
                  try wp_auto
                  -- the violation ends the search: the rest of the round skips
                  have hr5 : r5 = a'' := foldlM_take_fix _ _ _ _ _ _ hinner htake2 (fun l' =>
                    Trace.stepInnerF_foldlM_skip _ _ l' a'' (by rw [ha'']; rfl))
                  have hR2 : R = a' := foldlM_take_fix _ _ _ _ _ _ hR' htake (fun l' =>
                    Trace.stepOuterF_foldlM_skip _ _ _ l' a' (by rw [ha', hr5, ha'']; rfl))
                  have hrel := hcomp _ (Trace.StepLoop.violation fr (ou, vi, info) R.1 R.2.1 R.2.2.1 R.2.2.2 hfrne
                    (by rw [hR]) (by rw [hR2, ha', hr5, ha'']; rfl))
                  rw [hR2, ha', hr5, ha''] at hrel
                  simp only at hrel
                  wp_for_post
                  try wp_auto
                  wp_for_post
                  try wp_auto
                  wp_for_post
                  try wp_auto
                  iapply HΦ
                  iexists ou3, { info3 with violation := some w }
                  isplitr
                  · ipureintro
                    refine ⟨hrel, hbr3, ?_⟩
                    exact Hvgo
                  iunfold tstatesOut
                  iexists gou3
                  iframe
                  try iexact Houl
            | none =>
              rw [hff] at Hkf
              simp only at Hkf
              rw [decide_eq_true (show sint.Z kf < sint.Z (W64 0) by rw [Hkf]; have : sint.Z (W64 0) = 0 := rfl; omega)]
              have hmf := memEq_of_findIdx?_none hff
              simp only [hmf, Bool.false_eq_true, ↓reduceIte] at ha''
              try wp_auto
              wp_apply wp_slice_literal [gy]
              isplitr
              · ipureintro; rfl
              iintro %slf ⟨Hslf, -⟩
              try wp_auto
              wp_apply wp_slice_append $$ [Hfs Hfsc Hslf] as %fsl4 ⟨Hfs, Hfsc, -⟩
              · iframe
              try wp_auto
              ihave #Hfsl' : ([∗list] h;x ∈ gfs3 ++ [gy];fr3 ++ [y], tstateRO (GF := GF) h x) $$ []
              · iapply BigSepL2.bigSepL2_snoc.2
                iframe Hfsl Hgyy
              iclear Hfsl
              cases invariants
              · rw [Trace.stepNewInfo_false] at hni
                cases hni
                try simp only at ha''
                try wp_auto
                wp_for_post
                iframe
                iexists _, _, fsl4, nsl4, vsl4, osl3, (gfs3 ++ [gy]), (gnx3 ++ [gy]), (gvi3 ++ [gy]), gou3, ou3, (vi3 ++ [y]), (nx3 ++ [y]), (fr3 ++ [y]), info3, gi3
                iframe
                try iframe Houl
                try iframe Hvil
                try iframe Hnxl
                try iframe Hfsl
                try iframe Houl'
                try iframe Hvil'
                try iframe Hnxl'
                try iframe Hfsl'
                ipureintro
                refine ⟨by clear hacc3 htake2; word, by clear hacc3 htake2; word, by rw [hm1', htake2, ha''], hvn3, hbr3, hvs3, hnxN⟩
              · cases hv : y.s.violated with
                | error e => simp [Trace.stepNewInfo, hv, Bind.bind, Except.bind] at hni
                | ok r =>
                rw [Trace.stepNewInfo_true _ _ _ hv] at hni
                cases hni
                try simp only at ha''
                try wp_auto
                wp_apply wp_Violated gy.S' y.s r $$ [Hys] as %vgo %Hvgo
                · iframe Hys; ipureintro
                  have hvo := Hok2 rfl x succ y hxr hnext hyin
                  exact ⟨hvo.1, hvo.2, hv⟩
                cases r with
                | none =>
                  have hv0 : vgo = go!"" := (strRel_eq_iff Hvgo strRel_empty).2 rfl
                  subst hv0
                  try wp_auto
                  wp_for_post
                  iframe
                  iexists _, _, fsl4, nsl4, vsl4, osl3, (gfs3 ++ [gy]), (gnx3 ++ [gy]), (gvi3 ++ [gy]), gou3, ou3, (vi3 ++ [y]), (nx3 ++ [y]), (fr3 ++ [y]), info3, gi3
                  iframe
                  try iframe Houl
                  try iframe Hvil
                  try iframe Hnxl
                  try iframe Hfsl
                  try iframe Houl'
                  try iframe Hvil'
                  try iframe Hnxl'
                  try iframe Hfsl'
                  ipureintro
                  refine ⟨by clear hacc3 htake2; word, by clear hacc3 htake2; word, by rw [hm1', htake2, ha''], hvn3, hbr3, hvs3, hnxN⟩
                | some w =>
                  have hw := State.violated_some_ne hv
                  have hv0 : vgo ≠ go!"" := fun h => hw ((strRel_eq_iff Hvgo strRel_empty).1 h)
                  rw [decide_eq_false hv0]
                  try wp_auto
                  -- the violation ends the search: the rest of the round skips
                  have hr5 : r5 = a'' := foldlM_take_fix _ _ _ _ _ _ hinner htake2 (fun l' =>
                    Trace.stepInnerF_foldlM_skip _ _ l' a'' (by rw [ha'']; rfl))
                  have hR2 : R = a' := foldlM_take_fix _ _ _ _ _ _ hR' htake (fun l' =>
                    Trace.stepOuterF_foldlM_skip _ _ _ l' a' (by rw [ha', hr5, ha'']; rfl))
                  have hrel := hcomp _ (Trace.StepLoop.violation fr (ou, vi, info) R.1 R.2.1 R.2.2.1 R.2.2.2 hfrne
                    (by rw [hR]) (by rw [hR2, ha', hr5, ha'']; rfl))
                  rw [hR2, ha', hr5, ha''] at hrel
                  simp only at hrel
                  wp_for_post
                  try wp_auto
                  wp_for_post
                  try wp_auto
                  wp_for_post
                  try wp_auto
                  iapply HΦ
                  iexists ou3, { info3 with violation := some w }
                  isplitr
                  · ipureintro
                    refine ⟨hrel, hbr3, ?_⟩
                    exact Hvgo
                  iunfold tstatesOut
                  iexists gou3
                  iframe
                  try iexact Houl
      · -- the successors are done: `fresh`'s count, then the round's next state
        try wp_auto
        have hmx : sint.nat m = succ.length := by clear hacc3; rw [← Hsuccl0, Hsuccsl.1]; word
        rw [hmx, List.take_length, hinner] at hacc3
        cases hacc3
        ihave %Hfsl0 := BigSepL2.bigSepL2_length $$ Hfsl
        ihave %Hfssl := ownSlice_len $$ Hfs
        have hfl : sint.Z fsl3.len = (fr3.length : Int) := by rw [← Hfsl0, Hfssl.1]; word
        by_cases hb : 1 < fr3.length
        · rw [decide_eq_true (show sint.Z (W64 1) < sint.Z fsl3.len by rw [hfl]; have : sint.Z (W64 1) = 1 := rfl; omega)]
          wp_auto
          wp_for_post
          iframe
          iexists _, _, nsl3, vsl3, osl3, gnx3, gvi3, gou3, ou3, vi3, nx3, { info3 with branched := true }, _
          iframe
          try iframe Houl
          try iframe Hvil
          try iframe Hnxl
          try iframe Hfsl
          try iframe Houl'
          try iframe Hvil'
          try iframe Hnxl'
          try iframe Hfsl'
          ipureintro
          refine ⟨by clear hacc htake; word, by clear hacc htake; word, ?_, hvn3, rfl, hvs3, hnx3⟩
          rw [hk1', htake, ha']
          simp [hvn3, hb]
        · rw [decide_eq_false (show ¬ sint.Z (W64 1) < sint.Z fsl3.len by rw [hfl]; have : sint.Z (W64 1) = 1 := rfl; omega)]
          wp_auto
          wp_for_post
          iframe
          iexists _, _, nsl3, vsl3, osl3, gnx3, gvi3, gou3, ou3, vi3, nx3, info3, gi3
          iframe
          try iframe Houl
          try iframe Hvil
          try iframe Hnxl
          try iframe Hfsl
          try iframe Houl'
          try iframe Hvil'
          try iframe Hnxl'
          try iframe Hfsl'
          ipureintro
          refine ⟨by clear hacc htake; word, by clear hacc htake; word, ?_, hvn3, hbr3, hvs3, hnx3⟩
          rw [hk1', htake, ha']
          simp [hvn3, hb]
    · -- the round is over: `frontier = next`
      try wp_auto
      have hkx : sint.nat k = fr.length := by clear hacc; rw [← Hfrl0, Hfrsl.1]; word
      rw [hkx, List.take_length, hR'] at hacc
      cases hacc
      wp_for_post
      iframe
      iexists nsl, vsl2, osl2, gnx, gvi2, gou2, nx2, vi2, ou2, info2, gi2
      iframe
      ipureintro
      refine ⟨hvn2, hbr2, hvs2, ?_, hnx2⟩
      intro r hr
      exact hcomp r (Trace.StepLoop.round fr (ou, vi, info) ou2 vi2 nx2 info2 r hfrne hR
        (by rw [hvn2]; rfl) hr)
  · -- the frontier is empty: the search is over
    have hfr0 : fr = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [← Hfrl0, Hfrsl.1]; word
    subst hfr0
    have hrel := hcomp _ (Trace.StepLoop.done (ou, vi, info))
    try wp_auto
    iapply HΦ
    iexists ou, info
    isplitr
    · ipureintro; exact ⟨hrel, hbr, by rw [hvn]; exact hvs⟩
    iunfold tstatesOut
    iexists gou
    iframe

end proof

end Etcdraft
end EtcdGrove
end Perennial

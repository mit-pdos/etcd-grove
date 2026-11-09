/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `CheckTrace`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.CheckTrace
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__StepLine
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__Init
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Trace__Len
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
theorem CheckTrace.wp_proof
    (wp_Init : Trace.Init.spec (GF := GF) (hG := hG))
    (wp_Len : Trace.Len.spec (GF := GF) (hG := hG))
    (wp_StepLine : Trace.StepLine.spec (GF := GF) (hG := hG))
    (wp_indexOf : indexOf.spec (GF := GF) (hG := hG))
    (wp_Violated : State.Violated.spec (GF := GF) (hG := hG)) :
    CheckTrace.spec (GF := GF) (hG := hG) := by
  intro t tr invariants
  wp_start as ⟨#Ht, %Hok⟩
  open_trace
  have hlenb := Hv.len_lt
  wp_auto
  wp_apply wp_with_defer_recover as %defer %pnc Hdefer Hpnc
  try wp_auto
  wp_apply wp_Init t tr $$ [Ht] as %g0 #Hg0
  · iframe Ht
  try wp_auto
  wp_apply wp_slice_literal [g0]
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨Hfr, -⟩
  wp_auto
  obtain ⟨Hscope, Hbnd, Hnoerr⟩ := Hok
  have hFT : ¬ ((#false : val) = #true) := fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide)
  have hTT : ((#true : val) = #true) := rfl
  by_cases hI : invariants = true
  -- (the goals: the invariants checked, then not)
  rw [show (#invariants : val) = #true by rw [hI]]
  obtain ⟨r0, hr0⟩ : ∃ r0, tr.initState.s.violated = .ok r0 := by
    cases h : tr.initState.s.violated with
    | error e =>
      exfalso
      have := Hnoerr { evalError := some e, errLine := 0 } (by unfold CheckTraceRel; rw [hI]; simp [h])
      simp at this
    | ok r0 => exact ⟨r0, rfl⟩
  have hb0 := Hbnd _ Trace.Reach.init
  ihave #Hg0' := Hg0
  iunfold tstateRO at Hg0'
  icases Hg0' with ⟨#Hs0, %Hg0l⟩
  wp_auto
  icases ownSlice_elem_acc (sint.Z (W64 0)) g0 _ _ [g0] (by decide) (by simp) $$ Hfr with ⟨He, Hfrb⟩
  wp_auto
  ihave Hfr := Hfrb $$ He
  rw [show ([g0] : List G.TState).set (sint.Z (W64 0)).toNat g0 = [g0] by simp]
  wp_apply wp_Violated g0.S' tr.initState.s r0 $$ [Hs0] as %vgo %Hvgo
  · iframe Hs0; ipureintro; exact ⟨hb0.2.1.violOk.1, hb0.2.1.violOk.2, hr0⟩
  rcases r0 with _ | w
  rotate_left
  · -- the initial state violates an invariant: the result
    have hw := State.violated_some_ne hr0
    have hv0 : vgo ≠ go!"" := fun h => hw ((strRel_eq_iff Hvgo strRel_empty).1 h)
    rw [decide_eq_false (show ¬ vgo = [] from hv0)]
    try wp_auto
    icases ownSlice_elem_acc (sint.Z (W64 0)) g0 _ _ [g0] (by decide) (by simp) $$ Hfr with ⟨He, Hfrb⟩
    wp_auto
    wp_apply wp_recoverPanic $$ Hpnc as Hpnc
    try wp_auto
    iapply HΦ
    iexists { violation := some w, violLine := 0 }
    ipureintro
    refine ⟨?_, ?_⟩
    · unfold CheckTraceRel; rw [hI]; simp [hr0]
    · exact ⟨rfl, rfl, rfl, Hvgo, rfl, strRel_empty, rfl⟩
  -- the invariants not checked
  rw [show (#invariants : val) = #false by simp at hI; rw [hI]]
  have hstart : ∀ r', tr.CheckFromRel invariants tr.len 1 [tr.initState] {} r' → CheckTraceRel tr invariants r' := by
    intro r' h; unfold CheckTraceRel; simp at hI; rw [hI] at h ⊢; simpa using h
  wp_auto
  rotate_left
  -- the initial state's invariants hold
  have hv0 : vgo = go!"" := (strRel_eq_iff Hvgo strRel_empty).2 rfl
  subst hv0
  try wp_auto
  have hstart : ∀ r', tr.CheckFromRel invariants tr.len 1 [tr.initState] {} r' → CheckTraceRel tr invariants r' := by
    intro r' h; unfold CheckTraceRel; rw [hI] at h ⊢; simp only [↓reduceIte]; rw [hr0]; exact h
  iclear Hs0
  -- the search, line by line
  all_goals
    ihave IH : iprop(∃ (l : w64) (fsl : GoSlice) (gF : List G.TState) (F : List TState) (gr : G.Result) (b : Nat),
        "l" ∷ l_ptr ↦ l ∗ "frontier" ∷ frontier_ptr ↦ fsl ∗ "Hfr" ∷ fsl ↦* gF ∗
        "Hfrl" ∷ ([∗list] h;x ∈ gF;F, tstateRO (GF := GF) h x) ∗ "r" ∷ r_ptr ↦ gr ∗
        "%Hinv" ∷ ⌜1 ≤ sint.Z l ∧ sint.Z l ≤ (tr.len : Int) + 1 ∧ resultRel gr { branched := b } ∧
          (∀ x ∈ F, tr.Reach x ∧ (x.l : Int) = sint.Z l) ∧
          (∀ r', tr.CheckFromRel invariants (tr.len + 1 - sint.nat l) (sint.nat l) F { branched := b } r' →
            CheckTraceRel tr invariants r')⌝) $$ [l frontier Hfr r]
    · iexists _, _, [g0], [tr.initState], _, 0
      iframe
      isplitr
      · iapply BigSepL2.bigSepL2_cons.2; isplitr; iexact Hg0; iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
      ipureintro
      refine ⟨by decide, by have : sint.Z (W64 1) = 1 := rfl; omega, ⟨rfl, rfl, rfl, strRel_empty, rfl, strRel_empty, rfl⟩, ?_, ?_⟩
      · intro x hx; simp at hx; subst hx; exact ⟨.init, rfl⟩
      · have h1 : tr.len + 1 - sint.nat (W64 1) = tr.len := by
          rw [show sint.nat (W64 1) = 1 from rfl]; omega
        rw [h1]; exact hstart
    wp_for IH
    obtain ⟨hl1, hl2, hres, hF, hcomp⟩ := Hinv
    icases Hfrl with #Hfrl
    wp_apply wp_Len t tr $$ [Ht] as %nlen %Hnlen
    · iframe Ht
    obtain ⟨n, hn⟩ : ∃ n : Nat, sint.Z l = n := ⟨sint.nat l, by word⟩
    have hnl : sint.nat l = n := by word
    rw [hnl] at hcomp
    by_cases hc : sint.Z l ≤ sint.Z nlen
    · -- line `n`
      rw [decide_eq_true hc]
      simp only [_root_.decide_true, ↓reduceIte]
      have hnle : n ≤ tr.len := by omega
      have hn0 : n ≠ 0 := by omega
      obtain ⟨hl1', hl1n, hnW⟩ := w64_line_succ l n hn (by unfold numBound at hlenb; omega)
      ihave %HFl := BigSepL2.bigSepL2_length $$ Hfrl
      ihave %HFsl := ownSlice_len $$ Hfr
      try wp_auto
      ihave Hnil : (zero_val GoSlice : GoSlice) ↦* ([] : List G.TState) $$ []
      · iapply ownSlice_nil
      ihave Hnilc : ownSliceCap G.TState (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
      · iapply ownSliceCap_nil
      ihave IHk : iprop(∃ (k : w64) (tsv : G.TState) (nsl : GoSlice) (gN : List G.TState) (N : List TState)
          (gr2 : G.Result) (ai : StepInfo),
          "i" ∷ i_ptr ↦ k ∗ "ts" ∷ ts_ptr ↦ tsv ∗ "Hfr" ∷ fsl ↦* gF ∗
          "next" ∷ next_ptr ↦ nsl ∗ "Hnx" ∷ nsl ↦* gN ∗ "Hnxc" ∷ ownSliceCap G.TState nsl (DFrac.own 1) ∗
          "Hnxl" ∷ ([∗list] h;x ∈ gN;N, tstateRO (GF := GF) h x) ∗ "r" ∷ r_ptr ↦ gr2 ∗
          "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z fsl.len ∧ ai.violation = none ∧
            resultRel gr2 { branched := brOf ai.branched b n } ∧ (∀ s ∈ N, tr.Reach s ∧ s.l = n + 1) ∧
            (∀ res, tr.CheckLineRel invariants (F.drop (sint.nat k)) (N, ai) res →
              tr.CheckLineRel invariants F ([], {}) res)⌝)
          $$ [i ts Hfr next Hnil Hnilc r]
      · iexists _, _, _, [], [], gr, {}
        iframe
        isplitr
        · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
        ipureintro
        refine ⟨by word, by word, rfl, by rw [brOf_false]; exact hres, by simp, fun res h => ?_⟩
        rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero] at h
        exact h
      wp_for IHk
      obtain ⟨hk0, hk1, hvn, hres2, hN, hcl⟩ := Hk
      ihave %HFsl := ownSlice_len $$ Hfr
      by_cases Hif : sint.Z k < sint.Z fsl.len
      · -- the frontier's state `k`
        try simp only [decide_eq_true Hif, decide_eq_true hTT, _root_.decide_true, ↓reduceIte]
        have Hlt : sint.nat k < gF.length := by rw [HFsl.1]; word
        obtain ⟨gx, Hgx⟩ : ∃ gx, gF[sint.nat k]? = some gx := ⟨_, List.getElem?_eq_getElem Hlt⟩
        obtain ⟨x, Hx⟩ : ∃ x, F[sint.nat k]? = some x := ⟨_, List.getElem?_eq_getElem (HFl ▸ Hlt)⟩
        ihave #Hgxx := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => tstateRO (GF := GF) a b) Hgx Hx $$ Hfrl
        have hk1' : sint.nat (k + W64 1) = sint.nat k + 1 := by word
        have hxm : x ∈ F := List.mem_of_getElem? Hx
        obtain ⟨hxr, hxl⟩ := hF x hxm
        have hxln : x.l = n := by omega
        have hdrop : F.drop (sint.nat k) = x :: F.drop (sint.nat k + 1) := by
          obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.1 Hx
          rw [List.drop_eq_getElem_cons hlt, hget]
        have hnoe : ∀ e, ¬ tr.StepLineRel x invariants (.error e) := by
          intro e he
          have h1 := hcl _ (by rw [hdrop]; exact .error x _ (N, ai) e (by simp [hvn]) he)
          have h2 := hcomp _ (by
            rw [show tr.len + 1 - n = (tr.len - n) + 1 by omega]
            exact Trace.CheckFromRel.error _ n F _ e h1)
          have := Hnoerr _ h2
          simp at this
        try wp_auto
        try rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z fsl.len from ⟨hk0, Hif⟩))]
        wp_apply wp_load_slice_index _ (sint.Z k) gF (DFrac.own 1) gx hk0 $$ [Hfr] as Hfr
        · iframe Hfr; ipureintro; exact Hgx
        try wp_auto
        wp_apply wp_StepLine t tr gx x invariants $$ [Ht Hgxx] as %ssl %gi Hpost
        · iframe Ht Hgxx; ipureintro
          exact ⟨Trace.CheckTraceOk.stepLineOk (tr := tr) ⟨Hscope, Hbnd, Hnoerr⟩ hxr, hnoe⟩
        icases Hpost with ⟨%tss, %info, %Hst, Hss⟩
        obtain ⟨Hrel, Hgb, Hgv⟩ := Hst
        iunfold tstatesOut at Hss
        icases Hss with ⟨%gsucc, Hsucc, Hsuccc, #Hsuccl⟩
        try wp_auto
        rw [Hgb]
        have hbr2 : uint.nat gr2.Branched' = brOf ai.branched b n := hres2.2.1
        cases hib : info.branched
        -- (the goals: `info.Branched` false, then true)
        wp_auto
        ihave Hr3 : iprop(∃ gr3 : G.Result, r_ptr ↦ gr3 ∗
            ⌜resultRel gr3 { branched := brOf (ai.branched || info.branched) b n }⌝) $$ [r]
        · iexists gr2; iframe; ipureintro; rw [hib, Bool.or_false]; exact hres2
        rotate_left
        wp_auto
        have hbo : brOf (ai.branched || info.branched) b n = brOf true (brOf ai.branched b n) n := by
          rw [brOf_or _ _ _ _ hn0, hib]
        by_cases hz : gr2.Branched' = W64 0
        -- (the goals: `r.Branched` zero, then not, then `info.Branched` false)
        rw [decide_eq_true hz]
        wp_auto
        ihave Hr3 : iprop(∃ gr3 : G.Result, r_ptr ↦ gr3 ∗
            ⌜resultRel gr3 { branched := brOf (ai.branched || info.branched) b n }⌝) $$ [r]
        · iexists _; iframe; ipureintro
          have h0 : brOf ai.branched b n = 0 := by rw [← hbr2, hz]; rfl
          obtain ⟨h1, -, h3⟩ := hres2
          refine ⟨h1, ?_, h3⟩
          rw [hbo, h0]; simp [brOf, hnW]
        rotate_left
        rw [decide_eq_false hz]
        wp_auto
        ihave Hr3 : iprop(∃ gr3 : G.Result, r_ptr ↦ gr3 ∗
            ⌜resultRel gr3 { branched := brOf (ai.branched || info.branched) b n }⌝) $$ [r]
        · iexists _; iframe; ipureintro
          have h0 : brOf ai.branched b n ≠ 0 := by
            rw [← hbr2]; intro h; exact hz (by word)
          rw [hbo]
          have : brOf true (brOf ai.branched b n) n = brOf ai.branched b n := by
            generalize brOf ai.branched b n = c at h0 ⊢; simp [brOf, h0]
          rw [this]; exact hres2
        all_goals
          icases Hr3 with ⟨%gr3, r, %hres3⟩
          have hvne := Trace.StepLineRel.violation_ne hxr Hrel
          cases hiv : info.violation with
          | some v =>
            -- a violation: the result
            have hv0 : gi.Violation' ≠ [] := by
              intro h; rw [hiv] at Hgv; exact hvne v hiv ((strRel_eq_iff Hgv strRel_empty).1 h)
            rw [decide_eq_false hv0]
            wp_auto
            have hline : tr.CheckLineRel invariants F ([], {})
                (.ok (tss.foldl (fun nx s2 => if memEq nx s2 then nx else nx ++ [s2]) N,
                  { branched := ai.branched || info.branched, violation := info.violation })) :=
              hcl _ (by
                rw [hdrop]
                exact Trace.CheckLineRel.step_violation tr invariants x _ (N, ai) tss info (by simp [hvn]) Hrel
                  (by simp [hiv]))
            have hfrom : tr.CheckFromRel invariants (tr.len + 1 - n) n F { branched := b }
                { violation := some v, violLine := n, branched := brOf (ai.branched || info.branched) b n } := by
              rw [show tr.len + 1 - n = (tr.len - n) + 1 by omega]
              have h := Trace.CheckFromRel.violation (t := tr) (invariants := invariants) (tr.len - n) n F
                { branched := b } _ _ v hline (by simp [hiv])
              rw [brOf_result] at h
              exact h
            wp_for_post
            try wp_auto
            wp_for_post
            try wp_auto
            wp_apply wp_recoverPanic $$ Hpnc as Hpnc
            try wp_auto
            iapply HΦ
            iexists _
            ipureintro
            refine ⟨hcomp _ hfrom, ?_⟩
            obtain ⟨-, h2, -⟩ := hres3
            rw [hiv] at Hgv
            exact ⟨rfl, h2, rfl, Hgv, hnW, strRel_empty, rfl⟩
          | none =>
            have hv0 : gi.Violation' = [] := by
              rw [hiv] at Hgv; exact (strRel_eq_iff Hgv strRel_empty).2 rfl
            rw [decide_eq_true hv0]
            wp_auto
            ihave %Hsuccsl := ownSlice_len $$ Hsucc
            ihave %Hsuccl0 := BigSepL2.bigSepL2_length $$ Hsuccl
            have hreach := Trace.StepLineRel.reach hxr Hrel
            ihave IHj : iprop(∃ (j : w64) (s2v : G.TState) (nsl3 : GoSlice) (gN3 : List G.TState) (N3 : List TState),
                "i" ∷ i_ptr ↦ j ∗ "s2" ∷ s2_ptr ↦ s2v ∗ "Hsucc" ∷ ssl ↦* gsucc ∗
                "next" ∷ next_ptr ↦ nsl3 ∗ "Hnx" ∷ nsl3 ↦* gN3 ∗ "Hnxc" ∷ ownSliceCap G.TState nsl3 (DFrac.own 1) ∗
                "Hnxl" ∷ ([∗list] h;x ∈ gN3;N3, tstateRO (GF := GF) h x) ∗
                "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z ssl.len ∧
                  N3 = (tss.take (sint.nat j)).foldl (fun nx s2 => if memEq nx s2 then nx else nx ++ [s2]) N ∧
                  (∀ s ∈ N3, tr.Reach s ∧ s.l = n + 1)⌝) $$ [i s2 Hsucc next Hnx Hnxc Hnxl]
            · iexists _, _, _, _, N
              iframe
              ipureintro
              refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl, hN⟩
            wp_for IHj
            obtain ⟨hj0, hj1, hN3, hN3r⟩ := Hj
            by_cases Hjf : sint.Z j < sint.Z ssl.len
            · -- the successor `j`
              try simp only [decide_eq_true Hjf, decide_eq_true hTT, _root_.decide_true, ↓reduceIte]
              have Hlt2 : sint.nat j < gsucc.length := by rw [Hsuccsl.1]; word
              obtain ⟨gy, Hgy⟩ : ∃ gy, gsucc[sint.nat j]? = some gy := ⟨_, List.getElem?_eq_getElem Hlt2⟩
              obtain ⟨y, Hy⟩ : ∃ y, tss[sint.nat j]? = some y := ⟨_, List.getElem?_eq_getElem (Hsuccl0 ▸ Hlt2)⟩
              ihave #Hgyy := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => tstateRO (GF := GF) a b) Hgy Hy $$ Hsuccl
              have hj1' : sint.nat (j + W64 1) = sint.nat j + 1 := by word
              have htake : tss.take (sint.nat j + 1) = tss.take (sint.nat j) ++ [y] := by
                rw [List.take_add_one, Hy]; rfl
              obtain ⟨hyr, hyl⟩ := hreach y (List.mem_of_getElem? Hy)
              try wp_auto
              try rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ssl.len from ⟨hj0, Hjf⟩))]
              wp_apply wp_load_slice_index _ (sint.Z j) gsucc (DFrac.own 1) gy hj0 $$ [Hsucc] as Hsucc
              · iframe Hsucc; ipureintro; exact Hgy
              try wp_auto
              icases Hnxl with #Hnxl
              wp_apply wp_indexOf nsl3 (DFrac.own 1) gN3 N3 gy y $$ [Hnx Hnxl Hgyy] as %ko ⟨Hnx, %Hko⟩
              · iframe Hnx Hnxl Hgyy
              try wp_auto
              cases hfi : N3.findIdx? (fun us => us.eq y) with
              | some jj =>
                rw [hfi] at Hko
                simp only at Hko
                rw [decide_eq_false (show ¬ sint.Z ko < sint.Z (W64 0) by rw [Hko]; have : sint.Z (W64 0) = 0 := rfl; omega)]
                try wp_auto
                wp_for_post
                iframe
                iexists _, _, nsl3, gN3, N3
                iframe
                try iframe Hnxl
                ipureintro
                refine ⟨by word, by word, ?_, hN3r⟩
                rw [hj1', htake, List.foldl_append, ← hN3]
                simp [memEq_of_findIdx?_some hfi]
              | none =>
                rw [hfi] at Hko
                simp only at Hko
                rw [decide_eq_true (show sint.Z ko < sint.Z (W64 0) by rw [Hko]; have : sint.Z (W64 0) = 0 := rfl; omega)]
                try wp_auto
                wp_apply wp_slice_literal [gy]
                isplitr
                · ipureintro; rfl
                iintro %sly ⟨Hsly, -⟩
                try wp_auto
                wp_apply wp_slice_append $$ [Hnx Hnxc Hsly] as %nsl4 ⟨Hnx, Hnxc, -⟩
                · iframe
                try wp_auto
                ihave #Hnxl' : ([∗list] h;x ∈ gN3 ++ [gy];N3 ++ [y], tstateRO (GF := GF) h x) $$ []
                · iapply BigSepL2.bigSepL2_snoc.2
                  iframe Hnxl Hgyy
                wp_for_post
                iframe
                iexists _, _, nsl4, gN3 ++ [gy], N3 ++ [y]
                iframe
                try iframe Hnxl'
                ipureintro
                refine ⟨by word, by word, ?_, ?_⟩
                · rw [hj1', htake, List.foldl_append, ← hN3]
                  simp [memEq_of_findIdx?_none hfi]
                · intro s hs
                  rcases List.mem_append.1 hs with hs | hs
                  · exact hN3r s hs
                  · simp at hs; subst hs; exact ⟨hyr, by omega⟩
            · -- the successors are done: the frontier's next state
              try simp only [decide_eq_false Hjf, decide_eq_false hFT, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
              have hjx : sint.nat j = tss.length := by rw [← Hsuccl0, Hsuccsl.1]; word
              rw [hjx, List.take_length] at hN3
              try wp_auto
              wp_for_post
              iframe
              iexists _, _, nsl3, gN3, N3, gr3, { branched := ai.branched || info.branched, violation := info.violation }
              iframe
              ipureintro
              refine ⟨by word, by word, hiv, hres3, hN3r, fun res h => hcl res ?_⟩
              rw [hdrop]
              refine Trace.CheckLineRel.step x _ (N, ai) tss info res (by simp [hvn]) Hrel ?_
              rw [← hN3, ← hk1']
              exact h
      · -- the frontier is done: the line's states
        try simp only [decide_eq_false Hif, decide_eq_false hFT, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
        have hkx : sint.nat k = F.length := by rw [← HFl, HFsl.1]; word
        rw [hkx, List.drop_length] at hcl
        have hline := hcl _ (Trace.CheckLineRel.nil (N, ai))
        ihave %HNl := BigSepL2.bigSepL2_length $$ Hnxl
        ihave %HNsl := ownSlice_len $$ Hnx
        have hNlen : sint.Z nsl.len = (N.length : Int) := by rw [← HNl, HNsl.1]; word
        have hbr2 : uint.nat gr2.Branched' = brOf ai.branched b n := hres2.2.1
        try wp_auto
        by_cases hN0 : N = []
        · -- no state steps through the line
          subst hN0
          have hz : nsl.len = W64 0 := by
            have : sint.Z nsl.len = 0 := by simpa using hNlen
            word
          rw [decide_eq_true hz]
          try wp_auto
          wp_for_post
          try wp_auto
          wp_apply wp_recoverPanic $$ Hpnc as Hpnc
          try wp_auto
          iapply HΦ
          iexists { ({ branched := brOf ai.branched b n } : Result) with line := n }
          ipureintro
          refine ⟨hcomp _ ?_, ?_⟩
          · rw [show tr.len + 1 - n = (tr.len - n) + 1 by omega]
            have h := Trace.CheckFromRel.unmatched (t := tr) (invariants := invariants) (tr.len - n) n F
              { branched := b } ai hline hvn
            rw [brOf_result] at h
            exact h
          · obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := hres2
            exact ⟨h1, h2, hnW, h4, h5, h6, h7⟩
        · -- the next line's frontier
          have hz : nsl.len ≠ W64 0 := by
            intro h; rw [h] at hNlen; apply hN0; apply List.eq_nil_of_length_eq_zero
            have : sint.Z (W64 0) = 0 := rfl
            omega
          rw [decide_eq_false hz]
          try wp_auto
          have hcomp' : ∀ r', tr.CheckFromRel invariants (tr.len - n) (n + 1) N
              { branched := brOf (decide (N.length > 1)) (brOf ai.branched b n) n } r' →
              CheckTraceRel tr invariants r' := by
            intro r' h
            apply hcomp
            rw [show tr.len + 1 - n = (tr.len - n) + 1 by omega]
            refine Trace.CheckFromRel.step _ _ _ _ N ai r' hline hvn hN0 ?_
            rw [brOf_result, brOf_result]
            exact h
          by_cases h1 : 1 < N.length
          -- (the goals: two states or more and `r.Branched` zero, then not zero, then one state)
          rw [decide_eq_true (show sint.Z (W64 1) < sint.Z nsl.len by rw [hNlen]; have : sint.Z (W64 1) = 1 := rfl; omega)]
          try wp_auto
          by_cases hz2 : gr2.Branched' = W64 0
          rw [decide_eq_true hz2]
          try wp_auto
          ihave Hr4 : iprop(∃ gr4 : G.Result, r_ptr ↦ gr4 ∗
              ⌜resultRel gr4 { branched := brOf (decide (N.length > 1)) (brOf ai.branched b n) n }⌝) $$ [r]
          · iexists _; iframe; ipureintro
            have h0 : brOf ai.branched b n = 0 := by rw [← hbr2, hz2]; rfl
            obtain ⟨h1', -, h3⟩ := hres2
            refine ⟨h1', ?_, h3⟩
            rw [h0]; simp [brOf, hnW, h1]
          rotate_left
          rw [decide_eq_false hz2]
          try wp_auto
          ihave Hr4 : iprop(∃ gr4 : G.Result, r_ptr ↦ gr4 ∗
              ⌜resultRel gr4 { branched := brOf (decide (N.length > 1)) (brOf ai.branched b n) n }⌝) $$ [r]
          · iexists _; iframe; ipureintro
            have h0 : brOf ai.branched b n ≠ 0 := by
              rw [← hbr2]; intro h; exact hz2 (by word)
            have : brOf (decide (N.length > 1)) (brOf ai.branched b n) n = brOf ai.branched b n := by
              generalize brOf ai.branched b n = c at h0 ⊢; simp [brOf, h0]
            rw [this]; exact hres2
          rotate_left
          rw [decide_eq_false (show ¬ sint.Z (W64 1) < sint.Z nsl.len by rw [hNlen]; have : sint.Z (W64 1) = 1 := rfl; omega)]
          try wp_auto
          ihave Hr4 : iprop(∃ gr4 : G.Result, r_ptr ↦ gr4 ∗
              ⌜resultRel gr4 { branched := brOf (decide (N.length > 1)) (brOf ai.branched b n) n }⌝) $$ [r]
          · iexists _; iframe; ipureintro
            have : brOf (decide (N.length > 1)) (brOf ai.branched b n) n = brOf ai.branched b n := by
              have : decide (N.length > 1) = false := decide_eq_false (by omega)
              rw [this, brOf_false]
            rw [this]; exact hres2
          all_goals
            icases Hr4 with ⟨%gr4, r, %hres4⟩
            try wp_auto
            wp_apply wp_max_int
            try wp_auto
            wp_for_post
            iframe
            iexists _, _, gN, N, _, brOf (decide (N.length > 1)) (brOf ai.branched b n) n
            iframe
            ipureintro
            refine ⟨by omega, by omega, hres4, fun x hx => ⟨(hN x hx).1, by rw [hl1', (hN x hx).2]; push_cast; rfl⟩, ?_⟩
            rw [hl1n, show tr.len + 1 - (n + 1) = tr.len - n by omega]
            exact hcomp'
    · -- past the last line: the trace is matched
      rw [decide_eq_false hc, decide_eq_false (show ¬ ((#false : val) = #true) from fun h => absurd (GoGlobalContext.intoVal_inj_bool h) (by decide))]
      simp only [_root_.decide_true, Bool.false_eq_true, ↓reduceIte]
      have hnend : n = tr.len + 1 := by omega
      try wp_auto
      wp_apply wp_recoverPanic $$ Hpnc as Hpnc
      try wp_auto
      iapply HΦ
      iexists { ({ branched := b } : Result) with ok := true }
      ipureintro
      refine ⟨hcomp _ ?_, ?_⟩
      · rw [show tr.len + 1 - n = 0 by omega]; exact .stop _ _ _
      · obtain ⟨-, h2, h3, h4, h5, h6, h7⟩ := hres
        exact ⟨rfl, h2, h3, h4, h5, h6, h7⟩

end proof

end Etcdraft
end EtcdGrove
end Perennial

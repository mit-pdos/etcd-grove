/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__LeaderCompletenessInv`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__LeaderCompletenessInv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Committed
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__CurrentLeaders
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Entry__Equal
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.StateRead

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

/-! ## The transcription's loops, named -/

/-- Server `i`'s entry at `idx0` (`idx0` is TLA+'s `idx - 1`). -/
def lcEntry (st : State) (i : ID) (idx0 : Nat) : Entry := ((st.s i).log[idx0]?).getD default

/-- Leader `l` against server `i`'s committed entry at `idx0`. -/
def lcLeader (st : State) (i : ID) (idx0 : Nat) (l : ID) : EvalM Bool := do
  let entry := lcEntry st i idx0
  let vl := st.s l
  if vl.currentTerm > entry.term && vl.currentTerm ≥ (st.s i).currentTerm then
    let some e := vl.log[idx0]?
      | throw { what := "LeaderCompletenessInv: log[l][idx] past the log's end (l, idx, length)",
                a := l, b := idx0 + 1, c := vl.log.length }
    return e == entry
  else return true

/-- Server `i`'s committed entry at `idx0`, against every leader. -/
def lcIdx (st : State) (i : ID) (idx0 : Nat) : EvalM Bool := st.currentLeaders.allM (lcLeader st i idx0)

/-- Server `i`'s committed entries. -/
def lcServer (st : State) (i : ID) : EvalM Bool := do
  let c ← st.committed i
  (List.range c.length).allM (lcIdx st i)

theorem leaderCompletenessInv_eq (st : State) :
    st.leaderCompletenessInv = st.server.allM (lcServer st) := rfl

/-- A leader's outcome: its guard decides whether it is compared. -/
theorem lcLeader_ok (st : State) (i : ID) (idx0 : Nat) (l : ID) (r : Bool)
    (h : lcLeader st i idx0 l = .ok r) :
    ((st.s l).currentTerm > (lcEntry st i idx0).term ∧ (st.s l).currentTerm ≥ (st.s i).currentTerm →
      ∃ e, (st.s l).log[idx0]? = some e ∧ r = decide (e = lcEntry st i idx0)) ∧
    (¬ ((st.s l).currentTerm > (lcEntry st i idx0).term ∧ (st.s l).currentTerm ≥ (st.s i).currentTerm) →
      r = true) := by
  unfold lcLeader at h
  simp only at h
  split at h
  · rename_i hc
    refine ⟨fun _ => ?_, fun hg => absurd (by simpa using hc) hg⟩
    cases he : (st.s l).log[idx0]? with
    | none => rw [he] at h; cases h
    | some e => rw [he] at h; cases h; exact ⟨e, rfl, rfl⟩
  · rename_i hc
    refine ⟨fun hg => absurd (by simp [hg.1, hg.2]) hc, fun _ => ?_⟩
    cases h; rfl

/-- `Committed(i)` is no longer than `i`'s log. -/
theorem committed_length_le (st : State) (i : ID) (c : List Entry) (h : st.committed i = .ok c) :
    c.length ≤ (st.s i).log.length := by
  unfold State.committed subSeqM at h
  cases hs : subSeq (st.s i).log 1 (st.s i).commitIndex with
  | none => rw [hs] at h; cases h
  | some l =>
    rw [hs] at h; cases h
    unfold subSeq at hs
    split at hs
    · cases hs; simp
    · split at hs
      · cases hs
      · cases hs; simp only [List.length_take, List.length_drop]; omega

/-- A current leader is a server. -/
theorem currentLeaders_mem (st : State) (l : ID) (h : l ∈ st.currentLeaders) : l ∈ st.server :=
  (List.mem_filter.1 h).1

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

-- A leader passed: the leader loop's next round (hygiene off: it names the proof's hypotheses).
set_option hygiene false in
local macro "lc_cont" : tactic => `(tactic| (
    try wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [hm1']
    exact hc3t hG))

theorem State.LeaderCompletenessInv.wp_proof (wp_Committed : State.Committed.spec (GF := GF) (hG := hG))
    (wp_CurrentLeaders : State.CurrentLeaders.spec (GF := GF) (hG := hG))
    (wp_EntryEqual : Entry.Equal.spec (GF := GF) (hG := hG)) :
    State.LeaderCompletenessInv.spec (GF := GF) (hG := hG) := by
  intro p st b
  wp_start as ⟨#Hst, %Hlogs, %Hb⟩
  rw [leaderCompletenessInv_eq] at Hb
  ihave #Hst0 := Hst
  iunfold stateRO at Hst0
  icases Hst0 with ⟨%g, %sm, #Hp, #Hsrv, #HS, %Hkeys, %Hnd, #Hsrvs, #Hm, #Hpm, %Hrc⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  iunfold setRO at Hsrv
  icases Hsrv with ⟨%xs, #Hxs, %Hmap⟩
  ihave %Hlen := ownSlice_len $$ Hxs
  wp_auto
  wp_apply wp_CurrentLeaders p st $$ [Hst] as %lsl #Hlsl
  · iframe Hst
  try wp_auto
  rename_i gi_ptr
  irename : (gi_ptr ↦ zero_val w64 : IProp GF) => Hgi
  ihave IH : iprop(∃ (n x : w64),
      "i" ∷ i_ptr ↦ n ∗ "Hgi" ∷ gi_ptr ↦ x ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z g.Server'.len ∧
        (st.server.take (sint.nat n)).allM (lcServer st) = .ok true⌝)
      $$ [i Hgi]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.allM_nil]; rfl⟩
  wp_for IH
  obtain ⟨hn0, hn1, hnt⟩ := Hn
  wp_if_destruct
  · have Hlt : sint.nat n < xs.length := by rw [Hlen.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, xs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hsy := set_getElem Hmap Hy
    have Hyin : uint.nat y ∈ st.server := List.mem_of_getElem? Hsy
    have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    obtain ⟨c, hc, hcf, hct⟩ := allM_take_step (lcServer st) st.server (sint.nat n) (uint.nat y) b Hsy hnt Hb
    obtain ⟨cy, hcy, hce⟩ : ∃ cy, st.committed (uint.nat y) = .ok cy ∧
        (List.range cy.length).allM (lcIdx st (uint.nat y)) = .ok c := by
      have h := hc
      simp only [lcServer] at h
      cases hcy : st.committed (uint.nat y) with
      | error e => rw [hcy] at h; cases h
      | ok cy => rw [hcy] at h; exact ⟨cy, rfl, h⟩
    have hcyl := committed_length_le st (uint.nat y) cy hcy
    have hlogy := Hlogs _ Hyin
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z g.Server'.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index g.Server' (sint.Z n) xs DFrac.discard y hn0 $$ [Hxs] as -
    · isplitr
      · iexact Hxs
      ipureintro; exact Hy
    try wp_auto
    wp_apply wp_Committed p st y cy $$ [Hst] as %u #Hu
    · iframe Hst; ipureintro; exact ⟨Hyin, hcy⟩
    try wp_auto
    ihave #Hu0 := Hu
    iunfold logRO at Hu0
    icases Hu0 with ⟨%ces, #Hces, #Hcb⟩
    ihave %Hcl := ownSlice_len $$ Hces
    ihave %Hcbl := BigSepL2.bigSepL2_length $$ Hcb
    have hzu : sint.Z u.len = (cy.length : Int) := by rw [← Hcbl, Hcl.1]; word
    icases servers_at st sm y Hyin $$ Hsrvs with ⟨%qi, %Hqi, #Hvi⟩
    iunfold serverRO at Hvi
    icases Hvi with ⟨%gi, %mi, #Hqi', %Hfi, #Hlogi, -, -, -, -, -, -⟩
    icases typedPointsto_split _ _ _ $$ Hqi' with Hqif
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hqif
    ihave #Hlogi0 := Hlogi
    iunfold logRO at Hlogi0
    icases Hlogi0 with ⟨%esi, #Hesi, #Hbi⟩
    ihave %Hli := ownSlice_len $$ Hesi
    ihave %Hbli := BigSepL2.bigSepL2_length $$ Hbi
    have hzi : sint.Z gi.Log'.len = ((st.s (uint.nat y)).log.length : Int) := by rw [← Hbli, Hli.1]; word
    ihave #Hlsl0 := Hlsl
    iunfold setRO at Hlsl0
    icases Hlsl0 with ⟨%lxs, #Hlxs, %Hlmap⟩
    ihave %Hllen := ownSlice_len $$ Hlxs
    ihave IJ : iprop(∃ (k : w64),
        "idx" ∷ idx_ptr ↦ k ∗
        "%Hk" ∷ ⌜1 ≤ sint.Z k ∧ sint.Z k ≤ (cy.length : Int) + 1 ∧
          ((List.range cy.length).take (sint.nat k - 1)).allM (lcIdx st (uint.nat y)) = .ok true⌝)
        $$ [idx]
    · iexists _
      iframe
      ipureintro
      refine ⟨by word, by word, by rw [show sint.nat (W64 1) - 1 = 0 from rfl, List.take_zero, List.allM_nil]; rfl⟩
    wp_for IJ
    obtain ⟨hk0, hk1, hkt⟩ := Hk
    wp_if_destruct
    · have hidxlt : sint.nat k - 1 < cy.length := by word
      have hidxz : sint.Z (k - W64 1) = ((sint.nat k - 1 : Nat) : Int) := by word
      have hkn : ((sint.nat k : Nat) : Int) = sint.Z k := by word
      have hpos : 0 ≤ sint.Z (k - W64 1) := by rw [hidxz]; omega
      have hk1' : sint.nat (k + W64 1) - 1 = sint.nat k - 1 + 1 := by word
      have hlt1 : sint.nat k - 1 < esi.length := by omega
      have hlt2 : sint.nat k - 1 < (st.s (uint.nat y)).log.length := by omega
      obtain ⟨ei, Hei⟩ : ∃ e, esi[sint.nat k - 1]? = some e := ⟨_, List.getElem?_eq_getElem hlt1⟩
      obtain ⟨xe, Hxe⟩ : ∃ x, (st.s (uint.nat y)).log[sint.nat k - 1]? = some x :=
        ⟨_, List.getElem?_eq_getElem hlt2⟩
      ihave #Hexe := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hei Hxe $$ Hbi
      have hentry : lcEntry st (uint.nat y) (sint.nat k - 1) = xe := by simp [lcEntry, Hxe]
      have hrange : (List.range cy.length)[sint.nat k - 1]? = some (sint.nat k - 1) :=
        List.getElem?_range hidxlt
      obtain ⟨c2, hc2, hc2f, hc2t⟩ :=
        allM_take_step (lcIdx st (uint.nat y)) (List.range cy.length) (sint.nat k - 1) (sint.nat k - 1) c hrange hkt hce
      wp_apply wp_map_lookup1 $$ [HS] as -
      · iexact HS
      rw [Hqi]
      simp only [Option.getD_some]
      try wp_auto
      have hbi : 0 ≤ sint.Z (k - W64 1) ∧ sint.Z (k - W64 1) < sint.Z gi.Log'.len := by
        rw [hidxz, hzi]; omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true hbi)]
      wp_apply wp_load_slice_index gi.Log' (sint.Z (k - W64 1)) esi DFrac.discard ei hpos $$ [Hesi] as -
      · isplitr
        · iexact Hesi
        ipureintro; rw [hidxz, Int.toNat_natCast]; exact Hei
      try wp_auto
      ihave IL : iprop(∃ (m z : w64),
          "i" ∷ i_ptr ↦ m ∗ "l" ∷ l_ptr ↦ z ∗
          "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z lsl.len ∧
            (st.currentLeaders.take (sint.nat m)).allM (lcLeader st (uint.nat y) (sint.nat k - 1)) = .ok true⌝)
          $$ [i l]
      · iexists _, _
        iframe
        ipureintro
        refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.allM_nil]; rfl⟩
      wp_for IL
      obtain ⟨hm0, hm1, hmt⟩ := Hm
      wp_if_destruct
      · have Hlt3 : sint.nat m < lxs.length := by rw [Hllen.1]; word
        obtain ⟨lz, Hlz⟩ : ∃ z, lxs[sint.nat m]? = some z := ⟨_, List.getElem?_eq_getElem Hlt3⟩
        have Hsl := set_getElem Hlmap Hlz
        have Hlin : uint.nat lz ∈ st.server := currentLeaders_mem st _ (List.mem_of_getElem? Hsl)
        have hm1' : sint.nat (m + W64 1) = sint.nat m + 1 := by word
        obtain ⟨c3, hc3, hc3f, hc3t⟩ := allM_take_step (lcLeader st (uint.nat y) (sint.nat k - 1))
          st.currentLeaders (sint.nat m) (uint.nat lz) c2 Hsl hmt hc2
        have hl3 := lcLeader_ok st (uint.nat y) (sint.nat k - 1) (uint.nat lz) c3 hc3
        rw [hentry] at hl3
        rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z lsl.len from ⟨hm0, Hif⟩))]
        wp_apply wp_load_slice_index lsl (sint.Z m) lxs DFrac.discard lz hm0 $$ [Hlxs] as -
        · isplitr
          · iexact Hlxs
          ipureintro; exact Hlz
        try wp_auto
        icases servers_at st sm lz Hlin $$ Hsrvs with ⟨%ql, %Hql, #Hvl⟩
        iunfold serverRO at Hvl
        icases Hvl with ⟨%gl, %ml, #Hql', %Hfl, #Hlogl, -, -, -, -, -, -⟩
        icases typedPointsto_split _ _ _ $$ Hql' with Hqlf
        simp only [TypedPointsto.typedPointstoDef]
        iNamed Hqlf
        ihave #Hlogl0 := Hlogl
        iunfold logRO at Hlogl0
        icases Hlogl0 with ⟨%esl, #Hesl, #Hbl⟩
        ihave %Hll := ownSlice_len $$ Hesl
        ihave %Hbll := BigSepL2.bigSepL2_length $$ Hbl
        have hzl : sint.Z gl.Log'.len = ((st.s (uint.nat lz)).log.length : Int) := by rw [← Hbll, Hll.1]; word
        wp_apply wp_map_lookup1 $$ [HS] as -
        · iexact HS
        rw [Hql]
        simp only [Option.getD_some]
        try wp_auto
        ihave #Hexe0 := Hexe
        iunfold entryRO at Hexe0
        icases Hexe0 with ⟨%Hte, -⟩
        by_cases hg1 : xe.term < (st.s (uint.nat lz)).currentTerm
        · rw [decide_eq_true (show sint.Z ei.Term' < sint.Z gl.CurrentTerm' by rw [Hte.1, Hfl.1]; exact hg1)]
          try wp_auto
          wp_apply wp_map_lookup1 $$ [HS] as -
          · iexact HS
          rw [Hqi]
          simp only [Option.getD_some]
          try wp_auto
          by_cases hg2 : (st.s (uint.nat y)).currentTerm ≤ (st.s (uint.nat lz)).currentTerm
          · rw [decide_eq_true (show sint.Z gi.CurrentTerm' ≤ sint.Z gl.CurrentTerm' by rw [Hfi.1, Hfl.1]; exact hg2)]
            try wp_auto
            obtain ⟨e, he, hc3e⟩ := hl3.1 ⟨hg1, hg2⟩
            have hidxl : sint.nat k - 1 < (st.s (uint.nat lz)).log.length := (List.getElem?_eq_some_iff.1 he).1
            have hnl : ¬ sint.Z gl.Log'.len < sint.Z k := by rw [hzl]; omega
            rw [decide_eq_false hnl]
            try wp_auto
            have hlt3 : sint.nat k - 1 < esl.length := by omega
            obtain ⟨el, Hel⟩ : ∃ x, esl[sint.nat k - 1]? = some x := ⟨_, List.getElem?_eq_getElem hlt3⟩
            ihave #Hele := BigSepL2.bigSepL2_lookup (Φ := fun _ e x => entryRO (GF := GF) e x) Hel he $$ Hbl
            have hbl : 0 ≤ sint.Z (k - W64 1) ∧ sint.Z (k - W64 1) < sint.Z gl.Log'.len := by
              rw [hidxz, hzl]; omega
            rw [ite_eq_left_of_eq_true _ _ (eq_true hbl)]
            try wp_auto
            rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Entry.TypeAssumptions.ptr_Equal_unfold.method_unfold]
            try wp_auto
            wp_apply wp_load_slice_index gl.Log' (sint.Z (k - W64 1)) esl DFrac.discard el hpos $$ [Hesl] as -
            · isplitr
              · iexact Hesl
              ipureintro; rw [hidxz, Int.toNat_natCast]; exact Hel
            try wp_auto
            wp_apply wp_EntryEqual el e ei xe $$ [Hele Hexe]
            · iframe Hele Hexe
            try wp_auto
            by_cases heq : e = xe
            · rw [decide_eq_true heq]
              have hG : c3 = true := by rw [hc3e, decide_eq_true heq]
              lc_cont
            · rw [decide_eq_false heq]
              try wp_auto
              wp_for_post
              try wp_auto
              wp_for_post
              try wp_auto
              wp_for_post
              try wp_auto
              have hb : b = false := hcf (hc2f (hc3f (by rw [hc3e, decide_eq_false heq])))
              rw [hb]
              iapply HΦ; ipureintro; trivial
          · rw [decide_eq_false (show ¬ sint.Z gi.CurrentTerm' ≤ sint.Z gl.CurrentTerm' by rw [Hfi.1, Hfl.1]; exact hg2)]
            have hG : c3 = true := hl3.2 (fun h => hg2 h.2)
            lc_cont
        · rw [decide_eq_false (show ¬ sint.Z ei.Term' < sint.Z gl.CurrentTerm' by rw [Hte.1, Hfl.1]; exact hg1)]
          have hG : c3 = true := hl3.2 (fun h => hg1 h.1)
          lc_cont
      · -- every leader passed: the next index
        have hme : st.currentLeaders.length ≤ sint.nat m := by rw [← Hlmap, List.length_map, Hllen.1]; word
        have hG : c2 = true := allM_take_end _ st.currentLeaders (sint.nat m) c2 hme hmt hc2
        try wp_auto
        wp_for_post
        iframe
        iexists _
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [hk1']
        exact hc2t hG
    · -- every committed entry passed: server `y` passed
      have hke : (List.range cy.length).length ≤ sint.nat k - 1 := by rw [List.length_range]; word
      have hG : c = true := allM_take_end _ (List.range cy.length) (sint.nat k - 1) c hke hkt hce
      try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [hn1']
      exact hct hG
  · have hne : st.server.length ≤ sint.nat n := by
      rw [← Hmap, List.length_map, Hlen.1]; word
    have hb : b = true := allM_take_end (lcServer st) st.server (sint.nat n) b hne hnt Hb
    rw [hb]
    iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial

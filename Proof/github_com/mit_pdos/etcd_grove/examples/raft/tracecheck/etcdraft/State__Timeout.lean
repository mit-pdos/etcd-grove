/-
Lean-first (no Rocq counterpart). Layer C's Probe (2026-11-08): the proof of `State__Timeout`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Timeout
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__GetConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__mut

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

/-- `Timeout`'s new term, in words: no overflow below `numBound`. -/
theorem timeout_term (w : w64) (n : Int) (h : sint.Z w = n) (hn : numOk n) :
    sint.Z (w + W64 1) = n + 1 := by
  unfold numOk numBound at hn
  subst h
  word

-- The rest of `Timeout` once the role check has passed (`hrole`), shared by the follower and
-- the candidate branch (hygiene off: it names the proof's hypotheses).
set_option hygiene false in
local macro "timeout_tail" : tactic => `(tactic| (
  wp_auto
  wp_apply wp_GetConfig p st i $$ [Hst] as %sl #Hsl
  · iframe Hst; ipureintro; exact Hi
  wp_apply wp_Has sl _ i $$ [Hsl] as -
  · iexact Hsl
  by_cases hc : uint.nat i ∈ st.getConfig (uint.nat i)
  · rw [decide_eq_true hc]
    wp_auto
    wp_apply wp_clone p st $$ [Hst] as %t Ht
    · iexact Hst
    try wp_auto
    wp_apply wp_mut t st [] i $$ [Ht] as %c ⟨Hh, Hc⟩
    · iframe Ht; ipureintro; exact ⟨Hi, List.not_mem_nil, Hnd⟩
    try wp_auto
    iunfold serverOwn at Hc
    icases Hc with ⟨%gc, %mc, Hcp, %Hcf, #Hcl, #Hcr, #Hcg, Hcm, %Hcmi, #Hcc, #Hcd⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hcp with ⟨Hcp, %Hcnn⟩
    icases typedPointsto_split _ _ _ $$ Hcp with Hcpf
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hcpf
    simp only [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Candidate]
    iapply wp_fupd
    wp_auto
    ihave Hcp : c ↦ ({ gc with State' := (go!"StateCandidate"), CurrentTerm' := (gs.CurrentTerm' + W64 1), VotedFor' := i, VotesResponded' := slice.nil, VotesGranted' := slice.nil } : G.Server) $$ [-HΦ Hcm Hh]
    · iapply typedPointsto_combine _ _ _ Hcnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave #Hnil := ownSlice_nil (V := w64) (GF := GF) DfracDiscarded
    obtain ⟨v', hv'⟩ : ∃ v' : Server, v' = { st.s (uint.nat i) with
        state := candidate, currentTerm := (st.s (uint.nat i)).currentTerm + 1, votedFor := uint.nat i,
        votesResponded := [], votesGranted := [] } := ⟨_, rfl⟩
    ihave Hc : serverOwn (GF := GF) c v' $$ [Hcp Hcm]
    · iunfold serverOwn
      iexists _, mc
      subst hv'
      iframe Hcp Hcm Hcl Hcc Hcd
      isplitr
      · ipureintro
        refine ⟨timeout_term _ _ Hf.1 Hterm, ?_, rfl, Hcf.2.2.2.1, Hcf.2.2.2.2⟩
        exact (show strRel go!"StateCandidate" candidate by unfold strRel candidate; decide)
      isplitr
      · iunfold setRO; iexists []; iframe Hnil; ipureintro; rfl
      isplitr
      · iunfold setRO; iexists []; iframe Hnil; ipureintro; rfl
      ipureintro; exact Hcmi
    ihave Hs := stateOwnHole_close _ _ _ _ _ _ Hi Hnd $$ [Hh Hc]
    · iframe
    imod stateOwn_persist $$ Hs with Hs
    imodintro
    iapply HΦ
    have ht : st.timeout (uint.nat i) = some (st.upd (uint.nat i) (fun _ => v')) := by
      subst hv'
      unfold State.timeout
      simp only [hrole, Bool.true_and]
      rw [show (st.getConfig (uint.nat i)).contains (uint.nat i) = true by
        simpa [List.contains_iff_mem] using hc]
      rfl
    rw [ht]
    iexact Hs
  · rw [decide_eq_false hc]
    wp_auto
    iapply HΦ
    have : st.timeout (uint.nat i) = none := by
      unfold State.timeout
      simp only [hrole, Bool.true_and]
      rw [ite_eq_right (by simpa [List.contains_iff_mem] using hc)]
    rw [this]
    ipureintro; rfl))

theorem State.Timeout.wp_proof
    (wp_GetConfig : State.GetConfig.spec (GF := GF) (hG := hG))
    (wp_Has : Set.Has.spec (GF := GF) (hG := hG))
    (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_mut : State.mut.spec (GF := GF) (hG := hG)) :
    State.Timeout.spec (GF := GF) (hG := hG) := by
  intro p st i
  wp_start as ⟨#Hst, %Hi, %Hnd, %Hterm⟩
  ihave #Hst0 := Hst
  iunfold stateRO at Hst0
  icases Hst0 with ⟨%g, %sm, #Hp, #Hsrv, #Hm, %Hkeys, #Hsrvs, #Hb1, #Hb2, %Hrc⟩
  obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.1 Hi
  icases (BigSepL.bigSepL_lookup (Φ := fun _ j => iprop(∃ q : Loc, ⌜sm !! (W64 (Int.ofNat j)) = some q⌝ ∗
      serverRO (GF := GF) q (st.s j))) (List.getElem?_eq_some_iff.2 ⟨hk, hki⟩)) $$ Hsrvs with ⟨%q0, %Hq0, #Hsv⟩
  have Hii : W64 (Int.ofNat (uint.nat i)) = i := by apply BitVec.eq_of_toNat_eq; simp
  rw [Hii] at Hq0
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hpf
  wp_auto
  wp_apply wp_map_lookup1 $$ [Hm] as -
  · iexact Hm
  rw [Hq0]
  simp only [Option.getD_some]
  iunfold serverRO at Hsv
  icases Hsv with ⟨%gs, %mm, #Hq', %Hf, #Hlog, #Hvr, #Hvg, #Hmm, %Hmi, #Hcfg, #Hdur⟩
  icases typedPointsto_split _ _ _ $$ Hq' with Hqf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hqf
  wp_auto
  -- the role, as the Lean compares it (`strRel` is injective, and the constants evaluate)
  have hF : gs.State' = go!"StateFollower" ↔ (st.s (uint.nat i)).state = follower := by
    have hc : strRel go!"StateFollower" follower := by unfold strRel follower; decide
    exact ⟨fun h => strRel_inj (h ▸ Hf.2.1) hc, fun h => by rw [Hf.2.1.2, h]; exact hc.2.symm⟩
  have hC : gs.State' = go!"StateCandidate" ↔ (st.s (uint.nat i)).state = candidate := by
    have hc : strRel go!"StateCandidate" candidate := by unfold strRel candidate; decide
    exact ⟨fun h => strRel_inj (h ▸ Hf.2.1) hc, fun h => by rw [Hf.2.1.2, h]; exact hc.2.symm⟩
  by_cases h1 : (st.s (uint.nat i)).state = follower
  · rw [decide_eq_true (hF.2 h1)]
    have hrole : or ((st.s (uint.nat i)).state == follower) ((st.s (uint.nat i)).state == candidate) = true := by
      simp [h1]
    timeout_tail
  · rw [decide_eq_false (fun h => h1 (hF.1 h))]
    wp_auto
    by_cases h2 : (st.s (uint.nat i)).state = candidate
    · rw [decide_eq_true (hC.2 h2)]
      have hrole : or ((st.s (uint.nat i)).state == follower) ((st.s (uint.nat i)).state == candidate) = true := by
        simp [h2]
      timeout_tail
    · rw [decide_eq_false (fun h => h2 (hC.1 h))]
      wp_auto
      iapply HΦ
      have : st.timeout (uint.nat i) = none := by
        unfold State.timeout
        simp [h1, h2]
      rw [this]
      ipureintro; rfl

end proof

end Etcdraft
end EtcdGrove
end Perennial

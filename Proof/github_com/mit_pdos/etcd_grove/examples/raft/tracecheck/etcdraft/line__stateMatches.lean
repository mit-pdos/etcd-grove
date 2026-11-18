/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `line__stateMatches`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__stateMatches
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Equal

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

theorem line.stateMatches.wp_proof (wp_SetEqual : Set.Equal.spec (GF := GF) (hG := hG)) :
    line.stateMatches.spec (GF := GF) (hG := hG) := by
  intro q x p st i
  wp_start as ⟨#Hlp, #Hst⟩
  ihave HΦ' : (∀ b : Bool, ⌜b = x.stateMatches st (uint.nat i)⌝ -∗ Φ #b) $$ [HΦ]
  · iintro %b %hb; rw [hb]; iapply HΦ; ipureintro; trivial
  ihave #Hst0 := Hst
  iunfold stateRO at Hst0
  icases Hst0 with ⟨%g, %sm, #Hp, #Hsrv, #Hm, %Hkeys, %Hnd, #Hsrvs, #Hb1, #Hb2, %Hrc⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpf with ⟨#P1, #P2, #P3, #P4, #P5, #P6, #P7, -⟩
  open_lineP
  wp_auto
  wp_apply wp_map_lookup2 $$ [Hm] as -
  · iexact Hm
  by_cases Hi : uint.nat i ∈ st.server
  rotate_left
  · have hn : sm !! i = none := by
      cases h : sm !! i with
      | none => rfl
      | some _ => exact absurd ((Hkeys i).1 (by simp [h])) Hi
    rw [hn]
    simp only [Option.isSome_none, Option.getD_none, _root_.decide_false, Bool.false_eq_true]
    wp_auto
    iapply HΦ'; ipureintro
    simp [Line.stateMatches, Hi]
  icases servers_at st sm i Hi $$ Hsrvs with ⟨%q0, %Hq0, #Hsv⟩
  rw [Hq0]
  simp only [Option.isSome_some, Option.getD_some, _root_.decide_true]
  iunfold serverRO at Hsv
  icases Hsv with ⟨%gs, %mm, #Hq', %Hf, #Hlog, #Hvr, #Hvg, #Hmm, %Hmi, #Hcfg, #Hdur⟩
  icases typedPointsto_split _ _ _ $$ Hq' with Hqf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hqf with ⟨#V1, #V2, #V3, #V4, #V5, #V6, #V7, #V8, #V9, #V10, #V11, #V12, -⟩
  icases typedPointsto_split _ _ _ $$ State with Hesf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hesf with ⟨#ES1, #ES2, #ES3, -⟩
  wp_auto
  rw [decide_eq_decide.2 (sint_eq_iff _ _ _ _ Hf.1 Hef.2.2.1)]
  by_cases h1 : (st.s (uint.nat i)).currentTerm = x.ev.state.term
  rotate_left
  · rw [decide_eq_false h1]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.stateMatches, Hi, h1]
  rw [decide_eq_true h1]
  wp_auto
  rw [decide_strRel Hf.2.1 Hlf.2.2.1]
  by_cases h2 : (st.s (uint.nat i)).state = x.role
  rotate_left
  · rw [decide_eq_false h2]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.stateMatches, Hi, h1, h2]
  rw [decide_eq_true h2]
  wp_auto
  rw [decide_eq_decide.2 (uint_eq_iff _ _ _ _ Hf.2.2.1 Hlf.2.1)]
  by_cases h3 : (st.s (uint.nat i)).votedFor = x.vote
  rotate_left
  · rw [decide_eq_false h3]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.stateMatches, Hi, h1, h2, h3]
  rw [decide_eq_true h3]
  wp_auto
  ihave #Hlog0 := Hlog
  iunfold logRO at Hlog0
  icases Hlog0 with ⟨%es, #Hes, #Hel⟩
  ihave %Hesl := ownSlice_len $$ Hes
  ihave %Hell := BigSepL2.bigSepL2_length $$ Hel
  have hlen : sint.Z gs.Log'.len = ((st.s (uint.nat i)).log.length : Int) := by rw [← Hell, Hesl.1]; word
  rw [show decide (gs.Log'.len = ge.Log') = decide (((st.s (uint.nat i)).log.length : Int) = x.ev.log) from
    decide_eq_decide.2 (sint_eq_iff _ _ _ _ hlen Hef.2.2.2.2.2.2)]
  by_cases h4 : ((st.s (uint.nat i)).log.length : Int) = x.ev.log
  rotate_left
  · rw [decide_eq_false h4]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.stateMatches, Hi, h1, h2, h3, h4]
  rw [decide_eq_true h4]
  wp_auto
  rw [decide_eq_decide.2 (sint_eq_iff _ _ _ _ Hf.2.2.2.2.1 Hef.2.2.2.2.1)]
  by_cases h5 : (st.s (uint.nat i)).commitIndex = x.ev.state.commit
  rotate_left
  · rw [decide_eq_false h5]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.stateMatches, Hi, h1, h2, h3, h4, h5]
  rw [decide_eq_true h5]
  iunfold configRO at Hcfg
  icases Hcfg with ⟨%ja, %jb, %Hjab, #Hja, #Hjb, -⟩
  icases typedPointsto_split _ _ _ $$ V11 with Hcf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hcf with ⟨#J1, -⟩
  icases array_acc _ 0 _ _ _ ja (Int.le_refl _) (by rw [Hjab]; rfl) $$ J1 with ⟨#Hj0, -⟩
  icases array_acc _ 1 _ _ _ jb (by decide) (by rw [Hjab]; rfl) $$ J1 with ⟨#Hj1, -⟩
  icases array_acc _ 0 _ _ _ ca (Int.le_refl _) (by rw [Hcab]; rfl) $$ conf with ⟨#Hk0, -⟩
  icases array_acc _ 1 _ _ _ cb (by decide) (by rw [Hcab]; rfl) $$ conf with ⟨#Hk1, -⟩
  wp_auto
  try rw [show sint.Z (W64 0) = 0 from rfl]
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Equal_unfold.method_unfold]
  try rw [show sint.Z (W64 0) = 0 from rfl]
  wp_auto
  wp_apply wp_SetEqual _ _ _ _ $$ [Hja Hc0] as -
  · iframe Hja Hc0
  by_cases h6 : (st.s (uint.nat i)).config.incoming = x.conf.1
  rotate_left
  · rw [decide_eq_false h6]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.stateMatches, Hi, h1, h2, h3, h4, h5, h6]
  rw [decide_eq_true h6]
  wp_auto
  try rw [show sint.Z (W64 1) = 1 from rfl]
  wp_auto
  try rw [show sint.Z (W64 1) = 1 from rfl]
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Equal_unfold.method_unfold]
  try rw [show sint.Z (W64 1) = 1 from rfl]
  wp_auto
  wp_apply wp_SetEqual _ _ _ _ $$ [Hjb Hc1] as -
  · iframe Hjb Hc1
  try wp_auto
  iapply HΦ'; ipureintro
  by_cases h7 : (st.s (uint.nat i)).config.outgoing = x.conf.2 <;> simp [Line.stateMatches, Hi, h1, h2, h3, h4, h5, h6, h7]

end proof

end Etcdraft
end EtcdGrove
end Perennial

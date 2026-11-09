/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__AppendEntriesToSelf`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__AppendEntriesToSelf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__send

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

theorem State.AppendEntriesToSelf.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_send : State.send.spec (GF := GF) (hG := hG)) :
    State.AppendEntriesToSelf.spec (GF := GF) (hG := hG) := by
  intro p st i
  wp_start as ⟨#Hst, %Hi, %Hok⟩
  ihave #Hst0 := Hst
  iunfold stateRO at Hst0
  icases Hst0 with ⟨%g, %sm, #Hp, #Hsrv, #Hm, %Hkeys, %Hnd, #Hsrvs, #Hb1, #Hb2, %Hrc⟩
  obtain ⟨k, hk, hki⟩ := List.mem_iff_getElem.1 Hi
  icases (BigSepL.bigSepL_lookup (Φ := fun _ j => iprop(∃ q : Loc, ⌜sm !! (W64 (Int.ofNat j)) = some q⌝ ∗
      serverRO (GF := GF) q (st.s j))) (List.getElem?_eq_some_iff.2 ⟨hk, hki⟩)) $$ Hsrvs with ⟨%q0, %Hq0, #Hsv⟩
  have Hii : W64 (Int.ofNat (uint.nat i)) = i := by apply BitVec.eq_of_toNat_eq; simp
  rw [Hii] at Hq0
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpf with ⟨#P1, #P2, #P3, #P4, #P5, #P6, #P7, -⟩
  iapply wp_fupd
  wp_auto
  wp_apply wp_map_lookup1 $$ [Hm] as -
  · iexact Hm
  rw [Hq0]
  simp only [Option.getD_some]
  iunfold serverRO at Hsv
  icases Hsv with ⟨%gs, %mm, #Hq', %Hf, #Hlog, #Hvr, #Hvg, #Hmm, %Hmi, #Hcfg, #Hdur⟩
  icases typedPointsto_split _ _ _ $$ Hq' with Hqf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hqf with ⟨#V1, #V2, #V3, #V4, #V5, #V6, #V7, #V8, #V9, #V10, #V11, #V12, -⟩
  wp_auto
  have hL := strRel_eq_iff Hf.2.1 (show strRel go!"StateLeader" leader by unfold strRel leader; decide)
  by_cases hl : (st.s (uint.nat i)).state = leader
  · rw [decide_eq_true (hL.2 hl)]
    wp_auto
    wp_apply wp_clone p st $$ [Hst] as %t Ht
    · iexact Hst
    try wp_auto
    ihave #Hlog0 := Hlog
    iunfold logRO at Hlog0
    icases Hlog0 with ⟨%es, #Hes, #Hel⟩
    ihave %Hesl := ownSlice_len $$ Hes
    ihave %Hell := BigSepL2.bigSepL2_length $$ Hel
    ihave #Hnil := logRO_nil (GF := GF)
    irename «$a0» => Hmq
    ipersist Hmq
    ihave #Hmsg : msgRO (GF := GF) «$a0_ptr» { type := .appendEntriesResponse, subtype := "app", term := (st.s (uint.nat i)).currentTerm, success := true, matchIndex := (st.s (uint.nat i)).log.length, source := uint.nat i, dest := uint.nat i } $$ []
    · iunfold msgRO
      iexists _
      iframe Hmq Hnil
      ipureintro
      exact ⟨rfl, (show strRel go!"app" "app" by unfold strRel; decide), Hf.1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by rw [← Hell, Hesl.1]; word, rfl, rfl⟩
    wp_apply wp_send t st [] _ _ $$ [Ht Hmsg] as Ht
    · iframe Ht Hmsg; ipureintro; exact ⟨Hok.1, Hok.count_lt _⟩
    try wp_auto
    imod stateOwn_persist $$ Ht with #Ht
    imodintro
    iapply HΦ
    have : st.appendEntriesToSelf (uint.nat i) = some (st.send { type := .appendEntriesResponse, subtype := "app", term := (st.s (uint.nat i)).currentTerm, success := true, matchIndex := (st.s (uint.nat i)).log.length, source := uint.nat i, dest := uint.nat i }) := by
      unfold State.appendEntriesToSelf; simp [hl]
    rw [this]
    iexact Ht
  · rw [decide_eq_false (fun e => hl (hL.1 e))]
    wp_auto
    imodintro
    iapply HΦ
    have : st.appendEntriesToSelf (uint.nat i) = none := by
      unfold State.appendEntriesToSelf; simp [hl]
    rw [this]
    ipureintro; rfl

end proof

end Etcdraft
end EtcdGrove
end Perennial

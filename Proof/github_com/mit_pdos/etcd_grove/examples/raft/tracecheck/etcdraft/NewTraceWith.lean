/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `NewTraceWith`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.NewTraceWith
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.parseID
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.toSet
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.NewSet
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set__Subset
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.durableOf
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.isMessageEvent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.traceError
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.ParseRole

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

set_option maxHeartbeats 10000000 in
theorem NewTraceWith.wp_proof
    (wp_parseID : parseID.spec (GF := GF) (hG := hG))
    (wp_toSet : toSet.spec (GF := GF) (hG := hG))
    (wp_NewSet : NewSet.spec (GF := GF) (hG := hG))
    (wp_Subset : Set.Subset.spec (GF := GF) (hG := hG))
    (wp_durableOf : durableOf.spec (GF := GF) (hG := hG))
    (wp_isMessageEvent : isMessageEvent.spec (GF := GF) (hG := hG))
    (wp_traceError : traceError.spec (GF := GF) (hG := hG))
    (wp_ParseRole : ParseRole.spec (GF := GF) (hG := hG)) :
    NewTraceWith.spec (GF := GF) (hG := hG) := by
  intro sl evs pv cq
  wp_start as ⟨#Hevs, %Hb⟩
  ihave #Hevs0 := Hevs
  iunfold eventsRO at Hevs0
  icases Hevs0 with ⟨%gs, #Hgs, #Hge⟩
  ihave %Hgsl := ownSlice_len $$ Hgs
  ihave %Hgel := BigSepL2.bigSepL2_length $$ Hge
  wp_auto
  wp_if_destruct
  · wp_apply wp_traceError as %e %He
    try wp_auto
    iapply HΦ
    have : evs = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [← Hgel, Hgsl.1, Hif]; rfl
    subst this
    simp only [newTraceWith, List.isEmpty_nil, bind, Except.bind, throw, throwThe, MonadExceptOf.throw, ite_true]
    ipureintro; exact He
  have hne : evs ≠ [] := by
    intro h; subst h; apply Hif
    have h0 : gs.length = 0 := by simpa using Hgel
    have := Hgsl.1; rw [h0] at this; word
  try wp_auto
  icases typedPointsto_not_null_dup _ _ _ $$ «$r0» with ⟨Hr0, %Hr0nn⟩
  icases typedPointsto_split _ _ _ $$ Hr0 with Hr0f
  simp only [TypedPointsto.typedPointstoDef]
  icases Hr0f with ⟨lines, Server, InitSrv, bootstrap, init, PreVote, CheckQuorum, -⟩
  ihave Hnil : (slice.nil : GoSlice) ↦* ([] : List G.line) $$ []
  · iapply ownSlice_nil
  ihave Hcap0 : ownSliceCap G.line (slice.nil : GoSlice) (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IH : iprop(∃ (n kv : w64) (lsl : GoSlice) (lns : List G.line) (xs : List Line),
      "i" ∷ i_ptr ↦ n ∗ "k" ∷ k_ptr ↦ kv ∗ "lines" ∷ «$r0_ptr».[G.Trace, go!"lines"] ↦ lsl ∗
      "Hl" ∷ lsl ↦* lns ∗ "Hcap" ∷ ownSliceCap G.line lsl (DFrac.own 1) ∗
      "Hlr" ∷ ([∗list] ln;x ∈ lns;xs, lineRO ln x) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        (((List.range evs.length).zip evs).take (sint.nat n)).mapM (fun p => parseLine p.1 p.2) = .ok xs⌝)
      $$ [i k lines Hnil Hcap0]
  · iexists _, _, _, [], []
    iframe
    isplitl []
    · iapply BigSepL2.bigSepL2_nil.2; ipureintro; trivial
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl⟩
  wp_for IH
  obtain ⟨hn0, hn1, hacc⟩ := Hn
  wp_if_destruct
  · have Hnlt : sint.Z n < sint.Z sl.len := Hif
    have Hlt : sint.nat n < gs.length := by clear hacc; rw [Hgsl.1]; word
    obtain ⟨y, Hy⟩ : ∃ y, gs[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨x, Hx⟩ : ∃ x, evs[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem (Hgel ▸ Hlt)⟩
    ihave #Hyx := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => eventRO (GF := GF) a b) Hy Hx $$ Hge
    icases ownSlice_elem_acc (sint.Z n) y sl _ gs hn0 Hy $$ Hgs with ⟨#Hev, -⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) gs _ y hn0 $$ [] as -
    · iframe Hgs; ipureintro; exact Hy
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨hn0, Hif⟩))]
    ihave #Hyx0 := Hyx
    iunfold eventRO at Hyx0
    icases Hyx0 with ⟨%Hef, ⟨%ca, %cb, %Hcab, ⟨%cxs, #Hcxs, %Hcxr⟩, ⟨%cys, #Hcys, %Hcyr⟩⟩, #Hemsg, #Heprop⟩
    icases typedPointsto_split _ _ _ $$ Hev with Hevf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hevf with ⟨#EName, #ENID, #EState, #ERole, #ELog, #EConf, #EMsg, #EProp, -⟩
    icases typedPointsto_split _ _ _ $$ EState with Hesf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hesf with ⟨#ETerm, #EVote, #ECommit, -⟩
    wp_auto
    wp_apply wp_ParseRole
    try wp_auto
    icases typedPointsto_not_null_dup _ _ _ $$ ln with ⟨ln, %Hlnn⟩
    icases typedPointsto_split _ _ _ $$ ln with Hlnf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hlnf with ⟨Lev, Lnid, Lvote, Lrole, Lconf, Lfrom, Lto, -⟩
    wp_apply wp_parseID y.NID' x.nid $$ [] as %nid %okn %Hnid
    · ipureintro; exact Hef.2.1
    try wp_auto
    cases hpn : parseID x.nid with
    | none =>
      rw [hpn] at Hnid; rw [Hnid]
      wp_auto
      loop_fail (parse_err pv cq hne hacc Hx (by parse_fails [hpn]))
    | some vnid =>
    rw [hpn] at Hnid; obtain ⟨rfl, hnidv⟩ := Hnid
    wp_auto
    wp_apply wp_parseID y.State'.Vote' x.state.vote $$ [] as %vote %okv %Hvote
    · ipureintro; exact Hef.2.2.2.1
    try wp_auto
    cases hpv : parseID x.state.vote with
    | none =>
      rw [hpv] at Hvote; rw [Hvote]
      wp_auto
      loop_fail (parse_err pv cq hne hacc Hx (by parse_fails [hpn, hpv]))
    | some vvote =>
    rw [hpv] at Hvote; obtain ⟨rfl, hvotev⟩ := Hvote
    wp_auto
    ihave IHc : iprop(∃ (hv : w64) (a : GoArray GoSlice 2) (s0 s1 : GoSlice) (okv : Bool),
        "h" ∷ h_ptr ↦ hv ∗ "Lconf" ∷ ln_ptr.[G.line, go!"conf"] ↦ a ∗ "ok" ∷ ok_ptr ↦ okv ∗
        "%Ha" ∷ ⌜a.arr = [s0, s1] ∧ 0 ≤ sint.Z hv ∧ sint.Z hv ≤ 2⌝ ∗
        "Hc0" ∷ (if 1 ≤ sint.Z hv then iprop(∃ c0, ⌜toSet x.conf.1 = some c0⌝ ∗ setRO s0 c0) else True) ∗
        "Hc1" ∷ (if 2 ≤ sint.Z hv then iprop(∃ c1, ⌜toSet x.conf.2 = some c1⌝ ∗ setRO s1 c1) else True))
        $$ [h Lconf ok]
    · iexists _, _, slice.nil, slice.nil, _
      iframe
      have h1 : ¬ (1 ≤ sint.Z (W64 0)) := by word
      have h2 : ¬ (2 ≤ sint.Z (W64 0)) := by word
      simp only [h1, h2, ↓reduceIte]
      isplitl []
      · ipureintro; exact ⟨rfl, by word, by word⟩
      isplitl [] <;> ipureintro <;> trivial
    wp_for IHc
    obtain ⟨Ha, hh0, hh2⟩ := Ha
    wp_if_destruct
    · have hlt2 : sint.Z hv < 2 := by word
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z hv ∧ sint.Z hv < 2 from ⟨hh0, hlt2⟩))]
      have hcase : sint.Z hv = 0 ∨ sint.Z hv = 1 := by omega
      rcases hcase with hv0 | hv1
      · have hv0 : hv = W64 0 := by word
        subst hv0
        icases array_acc _ 0 _ _ _ ca (Int.le_refl _) (by rw [Hcab]; rfl) $$ EConf with ⟨#HC0, -⟩
        icases array_acc _ 0 _ _ _ s0 (Int.le_refl _) (by rw [Ha]; rfl) $$ Lconf with ⟨Hel, Hback⟩
        wp_auto
        rw [show sint.Z (W64 0) = 0 from rfl]
        wp_auto
        wp_apply wp_toSet ca _ cxs x.conf.1 $$ [] as %cset %okc ⟨-, Hcset⟩
        · iframe Hcxs; ipureintro; exact Hcxr
        try wp_auto
        cases htc : toSet x.conf.1 with
        | none =>
          simp only [htc]
          icases Hcset with %Hokc
          subst Hokc
          wp_auto
          loop_fail (parse_err pv cq hne hacc Hx (by parse_fails [hpn, hpv, htc]))
        | some c0 =>
        simp only [htc]
        icases Hcset with ⟨%Hokc, #Hc0set⟩
        subst Hokc
        wp_auto
        wp_for_post
        ihave Lconf := Hback $$ Hel
        iframe
        iexists _, _, cset, s1, _
        iframe
        have h1 : 1 ≤ sint.Z (W64 0 + W64 1) := by word
        have h2 : ¬ 2 ≤ sint.Z (W64 0 + W64 1) := by word
        simp only [h1, h2, ↓reduceIte]
        isplitl []
        · ipureintro; refine ⟨by rw [Ha]; rfl, by word, by word⟩
        isplitl []
        · iexists c0; iframe Hc0set; ipureintro; rfl
        ipureintro; trivial
      · have hv1 : hv = W64 1 := by word
        subst hv1
        have h1 : 1 ≤ sint.Z (W64 1) := by word
        have h2 : ¬ 2 ≤ sint.Z (W64 1) := by word
        simp only [h1, h2, ↓reduceIte]
        icases Hc0 with ⟨%c0, %Hc0e, #Hc0set⟩
        icases array_acc _ 1 _ _ _ cb (by decide) (by rw [Hcab]; rfl) $$ EConf with ⟨#HC1, -⟩
        icases array_acc _ 1 _ _ _ s1 (by decide) (by rw [Ha]; rfl) $$ Lconf with ⟨Hel, Hback⟩
        wp_auto
        rw [show sint.Z (W64 1) = 1 from rfl]
        wp_auto
        wp_apply wp_toSet cb _ cys x.conf.2 $$ [] as %cset %okc ⟨-, Hcset⟩
        · iframe Hcys; ipureintro; exact Hcyr
        try wp_auto
        cases htc : toSet x.conf.2 with
        | none =>
          simp only [htc]
          icases Hcset with %Hokc
          subst Hokc
          wp_auto
          loop_fail (parse_err pv cq hne hacc Hx (by parse_fails [hpn, hpv, Hc0e, htc]))
        | some c1 =>
        simp only [htc]
        icases Hcset with ⟨%Hokc, #Hc1set⟩
        subst Hokc
        wp_auto
        wp_for_post
        ihave Lconf := Hback $$ Hel
        iframe
        iexists _, _, s0, cset, _
        iframe
        have h1' : 1 ≤ sint.Z (W64 1 + W64 1) := by word
        have h2' : 2 ≤ sint.Z (W64 1 + W64 1) := by word
        simp only [h1', h2', ↓reduceIte]
        isplitl []
        · ipureintro; refine ⟨by rw [Ha]; rfl, by word, by word⟩
        isplitl []
        · iexists c0; iframe Hc0set; ipureintro; exact Hc0e
        iexists c1; iframe Hc1set; ipureintro; rfl
    have hv2 : hv = W64 2 := by word
    subst hv2
    have h1 : 1 ≤ sint.Z (W64 2) := by word
    have h2 : 2 ≤ sint.Z (W64 2) := by word
    simp only [h1, h2, ↓reduceIte]
    icases Hc0 with ⟨%c0, %Hc0e, #Hc0set⟩
    icases Hc1 with ⟨%c1, %Hc1e, #Hc1set⟩
    try wp_auto
    wp_apply wp_isMessageEvent y.Name' x.name $$ []
    · ipureintro; exact Hef.1
    try wp_auto
    ihave #Hpi := etcdraftInit_get $$ Hpkg
    icases Hpi with ⟨⟨%mrt, #Hmrt, #Hrtm⟩, -, -⟩
    by_cases Hmp : ¬ msgPass x
    · have Herr := parse_err pv cq hne hacc Hx (parseLine_err_msg hpn hpv Hc0e Hc1e Hmp)
      cases hm : x.msg with
      | none =>
        icases Hemsg with %Hmnull
        cases hme : isMessageEvent x.name
        · exact absurd ⟨by simp [hme], fun m h => by simp [hm] at h⟩ Hmp
        · wp_auto
          rw [Hmnull]
          wp_auto
          loop_fail Herr
      | some m =>
        icases Hemsg with ⟨%gm, #Hgm, %Hgmr⟩
        ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgm
        icases typedPointsto_split _ _ _ $$ Hgm with Hgmf
        simp only [TypedPointsto.typedPointstoDef]
        iNamed Hgmf
        cases hty : raftMsgType m.type with
        | some ty => exact absurd ⟨by simp [hm], fun m' h => by simp [hm] at h; subst h; simp [hty]⟩ Hmp
        | none =>
        cases hme : isMessageEvent x.name <;> wp_auto <;> (try rw [decide_eq_false Hnn]) <;> (try wp_auto) <;>
          (try rw [decide_eq_false Hnn]) <;> (try wp_auto)
        all_goals
          wp_apply wp_map_lookup2 $$ [Hrtm] as -
          · iexact Hrtm
          rw [raftMsgTypeMap_lookup Hgmr.1, hty]
          simp only [Option.map_none, Option.getD_none, Option.isSome_none, _root_.decide_false]
          wp_auto
          loop_fail Herr
    replace Hmp : msgPass x := Classical.not_not.mp Hmp
    wp_join at next with [ev]
    · cases hme : isMessageEvent x.name
      · wp_auto; wp_join_done
      · cases hm : x.msg with
        | none => exact absurd ⟨hme, hm⟩ Hmp.1
        | some m =>
          icases Hemsg with ⟨%gm, #Hgm, -⟩
          ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgm
          wp_auto
          rw [decide_eq_false Hnn]
          wp_auto
          wp_join_done
    wp_join at next with [ev]
    · cases hm : x.msg with
      | none =>
        icases Hemsg with %Hmnull
        rw [Hmnull]
        wp_auto
        wp_join_done
      | some m =>
        icases Hemsg with ⟨%gm, #Hgm, %Hgmr⟩
        ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgm
        icases typedPointsto_split _ _ _ $$ Hgm with Hgmf
        simp only [TypedPointsto.typedPointstoDef]
        iNamed Hgmf
        obtain ⟨ty, hty⟩ := msgPass_some hpn hpv Hc0e Hc1e Hmp hm
        try wp_auto
        rw [decide_eq_false Hnn]
        wp_auto
        wp_apply wp_map_lookup2 $$ [Hrtm] as -
        · iexact Hrtm
        rw [raftMsgTypeMap_lookup Hgmr.1, hty]
        simp only [Option.map_some, Option.getD_some, Option.isSome_some, _root_.decide_true]
        wp_auto
        wp_join_done
    rw [decide_strRel Hef.1 (show strRel go!"ChangeConf" "ChangeConf" by strRel_lit)]
    by_cases Hcp : ¬ ccPass x
    · have Herr := parse_err pv cq hne hacc Hx (parseLine_err_cc hpn hpv Hc0e Hc1e Hmp Hcp)
      have hcn : x.name = "ChangeConf" := by
        by_cases h : x.name = "ChangeConf"
        · exact h
        · exact absurd (fun h' => absurd h' h) Hcp
      rw [decide_eq_true hcn]
      wp_auto
      cases hp : x.prop with
      | none =>
        iunfold propsRO at Heprop
        icases Heprop with %Hpnull
        rw [Hpnull]
        wp_auto
        loop_fail Herr
      | some pr =>
        iunfold propsRO at Heprop
        icases Heprop with ⟨%gp, #Hgp, #Hccp⟩
        ihave %Hgpnn := typedPointsto_not_null _ _ _ $$ Hgp
        icases typedPointsto_split _ _ _ $$ Hgp with Hgpf
        simp only [TypedPointsto.typedPointstoDef]
        icases Hgpf with ⟨#PCC, -⟩
        rw [decide_eq_false Hgpnn]
        wp_auto
        cases hcc : pr.cc with
        | none =>
          icases Hccp with %Hccnull
          rw [Hccnull]
          wp_auto
          loop_fail Herr
        | some cc =>
          iunfold confChangeRO at Hccp
          icases Hccp with ⟨%gcc, #Hgcc, #Hchs, #Hnc⟩
          ihave %Hgccnn := typedPointsto_not_null _ _ _ $$ Hgcc
          icases typedPointsto_split _ _ _ $$ Hgcc with Hgccf
          simp only [TypedPointsto.typedPointstoDef]
          icases Hgccf with ⟨#CChanges, #CNewConf, -⟩
          rw [decide_eq_false Hgccnn]
          wp_auto
          cases hch : cc.changes with
          | none =>
            exact absurd (fun _ => ⟨cc, by simp [hp, hcc], by simp [hch]⟩) Hcp
          | some chs =>
            have hchs : chs = [] := by
              cases chs with
              | nil => rfl
              | cons c cs => exact absurd (fun _ => ⟨cc, by simp [hp, hcc], by simp [hch]⟩) Hcp
            subst hchs
            iunfold optSliceRO at Hchs
            icases Hchs with ⟨%csl, %cvs, #Hcp1, #Hcp2, %Hcvs⟩
            ihave %Hcsl := ownSlice_len $$ Hcp2
            ihave %hnn := typedPointsto_not_null _ _ _ $$ Hcp1
            rw [decide_eq_false hnn]
            wp_auto
            have hl0 : csl.len = W64 0 := by
              have : cvs = [] := by cases Hcvs; rfl
              subst this; simp at Hcsl; word
            rw [hl0]
            wp_auto
            loop_fail Herr
    replace Hcp : ccPass x := Classical.not_not.mp Hcp
    wp_join at next with [ev]
    · by_cases hcn : x.name = "ChangeConf"
      · rw [decide_eq_true hcn]
        obtain ⟨cc, hpc, hchn⟩ := Hcp hcn
        cases hp : x.prop with
        | none => simp [hp] at hpc
        | some pr =>
          have hcc : pr.cc = some cc := by simpa [hp] using hpc
          iunfold propsRO at Heprop
          icases Heprop with ⟨%gp, #Hgp, #Hccp⟩
          simp only [hcc]
          ihave %Hgpnn := typedPointsto_not_null _ _ _ $$ Hgp
          icases typedPointsto_split _ _ _ $$ Hgp with Hgpf
          simp only [TypedPointsto.typedPointstoDef]
          icases Hgpf with ⟨#PCC, -⟩
          iunfold confChangeRO at Hccp
          icases Hccp with ⟨%gcc, #Hgcc, #Hchs, #Hnc⟩
          ihave %Hgccnn := typedPointsto_not_null _ _ _ $$ Hgcc
          icases typedPointsto_split _ _ _ $$ Hgcc with Hgccf
          simp only [TypedPointsto.typedPointstoDef]
          icases Hgccf with ⟨#CChanges, #CNewConf, -⟩
          wp_auto
          rw [decide_eq_false Hgpnn]
          wp_auto
          rw [decide_eq_false Hgccnn]
          wp_auto
          cases hchv : cc.changes with
          | none =>
            iunfold optSliceRO at Hchs
            icases Hchs with %Hchnull
            rw [Hchnull]
            wp_auto
            wp_join_done
          | some chs =>
            iunfold optSliceRO at Hchs
            icases Hchs with ⟨%csl, %cvs, #Hcp1, #Hcp2, %Hcvs⟩
            ihave %Hcsl := ownSlice_len $$ Hcp2
            ihave %hnn := typedPointsto_not_null _ _ _ $$ Hcp1
            rw [decide_eq_false hnn]
            wp_auto
            have hl0 : ¬ csl.len = W64 0 := by
              have h1 := Hcvs.length_eq
              have h2 : chs ≠ [] := fun h => hchn (by rw [hchv, h])
              have h3 : chs.length ≠ 0 := fun h => h2 (List.eq_nil_of_length_eq_zero h)
              intro h; rw [h] at Hcsl; rw [h1] at Hcsl; apply h3; have := Hcsl.1; word
            rw [decide_eq_false hl0]
            wp_auto
            wp_join_done
      · rw [decide_eq_false hcn]
        wp_auto
        wp_join_done
    by_cases Hftn : ftOf x = none
    · have Herr := parse_err pv cq hne hacc Hx (parseLine_err_ft hpn hpv Hc0e Hc1e Hmp Hcp Hftn)
      cases hm : x.msg with
      | none => simp [ftOf, hm] at Hftn
      | some m =>
        icases Hemsg with ⟨%gm, #Hgm, %Hgmr⟩
        ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgm
        icases typedPointsto_split _ _ _ $$ Hgm with Hgmf
        simp only [TypedPointsto.typedPointstoDef]
        iNamed Hgmf
        rw [decide_eq_false Hnn]
        wp_auto
        wp_apply wp_parseID gm.From' m.from $$ [] as %fw %okf %Hfw
        · ipureintro; exact Hgmr.2.2.1
        cases hf : parseID m.from with
        | none =>
          rw [hf] at Hfw; rw [Hfw]
          wp_auto
          loop_fail Herr
        | some f =>
          rw [hf] at Hfw; obtain ⟨rfl, -⟩ := Hfw
          wp_auto
          wp_apply wp_parseID gm.To' m.to $$ [] as %tw %okt %Htw
          · ipureintro; exact Hgmr.2.2.2.1
          cases ht : parseID m.to with
          | none =>
            rw [ht] at Htw; rw [Htw]
            wp_auto
            loop_fail Herr
          | some t => simp [ftOf, hm, hf, ht] at Hftn
    obtain ⟨⟨f, t⟩, Hft⟩ : ∃ p, ftOf x = some p := Option.ne_none_iff_exists'.1 Hftn
    wp_join iprop(∃ (fw tw : w64) (okv : Bool), "Lfrom" ∷ ln_ptr.[G.line, go!"from"] ↦ fw ∗
        "Lto" ∷ ln_ptr.[G.line, go!"to"] ↦ tw ∗ "ok" ∷ ok_ptr ↦ okv ∗
        "ev" ∷ ev_ptr ↦ sliceIndexRef G.Event (sint.Z n) sl ∗ "%Hfw" ∷ ⌜uint.nat fw = f ∧ uint.nat tw = t⌝)
      at next with [Lfrom Lto ok ev] as ⟨%fw, %tw, %okv, Lfrom, Lto, ok, ev, %Hfw⟩
    · cases hm : x.msg with
      | none =>
        icases Hemsg with %Hmnull
        rw [Hmnull]
        wp_auto
        wp_join_done
        simp only [ftOf, hm, Option.some.injEq, Prod.mk.injEq] at Hft
        obtain ⟨rfl, rfl⟩ := Hft
        iexists _, _, _
        iframe
        ipureintro; exact ⟨rfl, rfl⟩
      | some m =>
        icases Hemsg with ⟨%gm, #Hgm, %Hgmr⟩
        ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgm
        icases typedPointsto_split _ _ _ $$ Hgm with Hgmf
        simp only [TypedPointsto.typedPointstoDef]
        iNamed Hgmf
        rw [decide_eq_false Hnn]
        wp_auto
        simp only [ftOf, hm] at Hft
        cases hf : parseID m.from <;> cases ht : parseID m.to <;> simp only [hf, ht, reduceCtorEq] at Hft
        simp only [Option.some.injEq, Prod.mk.injEq] at Hft
        obtain ⟨rfl, rfl⟩ := Hft
        wp_apply wp_parseID gm.From' m.from $$ [] as %fw %okf %Hfw
        · ipureintro; exact Hgmr.2.2.1
        rw [hf] at Hfw; obtain ⟨rfl, hfw⟩ := Hfw
        wp_auto
        wp_apply wp_parseID gm.To' m.to $$ [] as %tw %okt %Htw
        · ipureintro; exact Hgmr.2.2.2.1
        rw [ht] at Htw; obtain ⟨rfl, htw⟩ := Htw
        wp_auto
        wp_join_done
        iexists _, _, _
        iframe
        ipureintro; exact ⟨hfw, htw⟩
    ihave Hln : ln_ptr ↦ (⟨sliceIndexRef G.Event (sint.Z n) sl, nid, vote, y.Role', a, fw, tw⟩ : G.line)
        $$ [Lev Lnid Lvote Lrole Lconf Lfrom Lto]
    · iapply typedPointsto_combine _ _ _ Hlnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave #Hnewl : lineRO (⟨sliceIndexRef G.Event (sint.Z n) sl, nid, vote, y.Role', a, fw, tw⟩ : G.line)
        { ev := x, nid := vnid, vote := vvote, role := x.role, conf := (c0, c1), «from» := f, to := t } $$ []
    · iunfold lineRO
      isplitl []
      · iexists y; iframe Hev Hyx
      isplitl []
      · ipureintro; exact ⟨hnidv, hvotev, Hef.2.2.2.2.2.1, Hfw.1, Hfw.2⟩
      iexists s0, s1
      isplitl []
      · ipureintro; exact Ha
      iframe Hc0set Hc1set
    have hpl := parseLine_ok (k := sint.nat n) hpn hpv Hc0e Hc1e Hmp Hcp Hft
    have hacc' := parse_ok_step hacc Hx hpl
    wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl0 ⟨Hsl0, -⟩
    try wp_auto
    wp_apply wp_slice_append $$ [Hl Hcap Hsl0] as %s2 ⟨Hs2, Hcap2, -⟩
    · iframe
    try wp_auto
    wp_for_post
    iframe
    iexists _, _, _, _, _
    iframe
    isplitl [Hlr]
    · iapply BigSepL2.bigSepL2_snoc.2
      isplitl [Hlr]
      · iexact Hlr
      iexact Hnewl
    ipureintro
    have hn1' : sint.nat (n + W64 1) = sint.nat n + 1 := by
      have : sint.Z n < sint.Z sl.len := Hnlt
      clear hacc hacc'; word
    refine ⟨by clear hacc hacc'; word, by clear hacc hacc'; word, ?_⟩
    rw [hn1']; exact hacc'
  -- the lines are parsed
  have hnx : sint.nat n = evs.length := by clear hacc; rw [← Hgel, Hgsl.1]; word
  have hz : ((List.range evs.length).zip evs).length = evs.length := by simp
  rw [hnx, List.take_of_length_le (by rw [hz]; exact Nat.le_refl _)] at hacc
  have hxl : xs.length = evs.length := by rw [mapM_ok_length _ _ _ hacc, hz]
  ihave %Hlsl := ownSlice_len $$ Hl
  ihave %Hlnl := BigSepL2.bigSepL2_length $$ Hlr
  imod ownSlice_persist $$ Hl with #Hl
  icases Hlr with #Hlr
  ihave Hsnil : (zero_val GoSlice : GoSlice) ↦* ([] : List w64) $$ []
  · iapply ownSlice_nil
  ihave Hscap0 : ownSliceCap w64 (zero_val GoSlice : GoSlice) (DFrac.own 1) $$ []
  · iapply ownSliceCap_nil
  ihave IHs : iprop(∃ (m : w64) (lv : G.line) (ssl : GoSlice) (ws : List w64) (ad : List (Option ID)),
      "i" ∷ i_ptr ↦ m ∗ "ln" ∷ ln_ptr ↦ lv ∗ "server" ∷ server_ptr ↦ ssl ∗ "Hs" ∷ ssl ↦* ws ∗
      "Hscap" ∷ ownSliceCap w64 ssl (DFrac.own 1) ∗
      "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ sint.Z lsl.len ∧
        (xs.take (sint.nat m)).mapM addedServer = .ok ad ∧
        ∀ z, z ∈ ws.map (fun w => uint.nat w) ↔ z ∈ (xs.take (sint.nat m)).map Line.nid ++ ad.filterMap id⌝)
      $$ [i ln server Hsnil Hscap0]
  · iexists _, _, _, [], []
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl, ?_⟩
    intro z; rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for IHs
  obtain ⟨hm0, hm1, hmacc, hmmem⟩ := Hm
  wp_if_destruct
  · have Hmlt : sint.Z m < sint.Z lsl.len := Hif
    have Hlt : sint.nat m < lns.length := by clear hmacc hmmem; rw [Hlsl.1]; word
    obtain ⟨lg, Hlg⟩ : ∃ v, lns[sint.nat m]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨xl, Hxl⟩ : ∃ v, xs[sint.nat m]? = some v := ⟨_, List.getElem?_eq_getElem (Hlnl ▸ Hlt)⟩
    ihave #Hlgx := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => lineRO (GF := GF) a b) Hlg Hxl $$ Hlr
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z lsl.len from ⟨hm0, Hmlt⟩))]
    wp_apply wp_load_slice_index _ (sint.Z m) lns _ lg hm0 $$ [] as -
    · iframe Hl; ipureintro; exact Hlg
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    try wp_auto
    wp_apply wp_slice_append $$ [Hs Hscap Hsl1] as %s2 ⟨Hs2, Hscap2, -⟩
    · iframe
    try wp_auto
    ihave #Hlgx0 := Hlgx
    iunfold lineRO at Hlgx0
    icases Hlgx0 with ⟨⟨%ge, #Hgev, #Hger⟩, %Hlf, %la, %lb, %Hlab, #Hl0, #Hl1⟩
    iunfold eventRO at Hger
    icases Hger with ⟨%Hef2, -, #Hemsg2, #Heprop2⟩
    icases typedPointsto_split _ _ _ $$ Hgev with Hgevf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hgevf with ⟨#GName, -, -, -, -, -, -, #GProp, -⟩
    by_cases Hbad : addedBad xl
    · have Herr := added_err pv cq hne hacc hmacc Hxl (addedServer_bad Hbad)
      obtain ⟨hcn, c, cs, hchb, ha, hpj⟩ := Hbad
      cases hp : xl.ev.prop with
      | none => simp [hp] at hchb
      | some pr =>
      cases hcc : pr.cc with
      | none => simp [hp, hcc] at hchb
      | some cc =>
      have hch : cc.changes = some (c :: cs) := by simpa [hp, hcc] using hchb
      wp_auto
      rw [decide_strRel Hef2.1 (show strRel go!"ChangeConf" "ChangeConf" by strRel_lit), decide_eq_true hcn]
      iunfold propsRO at Heprop2
      icases Heprop2 with ⟨%gp, #Hgp, #Hccp⟩
      simp only [hcc]
      ihave %Hgpnn := typedPointsto_not_null _ _ _ $$ Hgp
      icases typedPointsto_split _ _ _ $$ Hgp with Hgpf
      simp only [TypedPointsto.typedPointstoDef]
      icases Hgpf with ⟨#PCC, -⟩
      wp_auto
      rw [decide_eq_false Hgpnn]
      wp_auto
      iunfold confChangeRO at Hccp
      icases Hccp with ⟨%gcc, #Hgcc, #Hchs, #Hnc⟩
      ihave %Hgccnn := typedPointsto_not_null _ _ _ $$ Hgcc
      icases typedPointsto_split _ _ _ $$ Hgcc with Hgccf
      simp only [TypedPointsto.typedPointstoDef]
      icases Hgccf with ⟨#CChanges, #CNewConf, -⟩
      rw [decide_eq_false Hgccnn]
      wp_auto
      simp only [hch]
      iunfold optSliceRO at Hchs
      icases Hchs with ⟨%csl, %cvs, #Hcp1, #Hcp2, %Hcvs⟩
      ihave %Hcsl := ownSlice_len $$ Hcp2
      ihave %hnn := typedPointsto_not_null _ _ _ $$ Hcp1
      rw [decide_eq_false hnn]
      wp_auto
      cases Hcvs with
      | cons hgc Hrest =>
      rename_i gc gcs
      have hl0 : sint.Z (W64 0) < sint.Z csl.len := by simp at Hcsl; word
      rw [decide_eq_true hl0]
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z csl.len from
        ⟨by word, hl0⟩))]
      wp_apply wp_load_slice_index _ (sint.Z (W64 0)) (gc :: gcs) _ gc (by word) $$ [] as -
      · iframe Hcp2; ipureintro; rfl
      try wp_auto
      rw [decide_strRel hgc.2 (show strRel go!"AddNewServer" "AddNewServer" by strRel_lit)]
      have hadd : decide (c.action = "AddNewServer") = true ∨
          decide (c.action = "AddNewServer") = false ∧ decide (c.action = "AddLearner") = true := by
        by_cases h1 : c.action = "AddNewServer"
        · exact .inl (decide_eq_true h1)
        · exact .inr ⟨decide_eq_false h1, decide_eq_true (ha.resolve_left h1)⟩
      rcases hadd with h | ⟨h1, h2⟩
      all_goals first
        | (rw [h]; wp_auto)
        | (rw [h1]; wp_auto
           rw [decide_strRel hgc.2 (show strRel go!"AddLearner" "AddLearner" by strRel_lit), h2]; wp_auto)
      all_goals
        wp_apply wp_parseID gc.NID' c.nid $$ [] as %j %okj %Hj
        · ipureintro; exact hgc.1
        rw [hpj] at Hj; rw [Hj]
        wp_auto
        loop_fail Herr
    obtain ⟨o, ho⟩ := addedServer_ok Hbad
    wp_join iprop(∃ (s3 : GoSlice) (ws3 : List w64), "server" ∷ server_ptr ↦ s3 ∗ "Hs" ∷ s3 ↦* ws3 ∗
        "Hscap" ∷ ownSliceCap w64 s3 (DFrac.own 1) ∗ "ev" ∷ ev_ptr ↦ lg.ev' ∗
        "%Hws3" ∷ ⌜ws3.map (fun w => uint.nat w) = (ws ++ [lg.nid']).map (fun w => uint.nat w) ++ o.toList⌝)
      at (if: _ then _ else _) with [server Hs2 Hscap2 ev] as ⟨%s3, %ws3, server, Hs, Hscap, ev, %Hws3⟩
    · wp_auto
      rw [decide_strRel Hef2.1 (show strRel go!"ChangeConf" "ChangeConf" by strRel_lit)]
      by_cases hcn : ¬ xl.ev.name = "ChangeConf"
      · rw [decide_eq_false hcn]
        wp_auto
        skip_leaf [hcn]
      replace hcn : xl.ev.name = "ChangeConf" := Classical.not_not.mp hcn
      rw [decide_eq_true hcn]
      cases hp : xl.ev.prop with
      | none =>
        iunfold propsRO at Heprop2
        icases Heprop2 with %Hpnull
        wp_auto
        rw [Hpnull]
        wp_auto
        skip_leaf [hcn, hp]
      | some pr =>
      iunfold propsRO at Heprop2
      icases Heprop2 with ⟨%gp, #Hgp, #Hccp⟩
      ihave %Hgpnn := typedPointsto_not_null _ _ _ $$ Hgp
      icases typedPointsto_split _ _ _ $$ Hgp with Hgpf
      simp only [TypedPointsto.typedPointstoDef]
      icases Hgpf with ⟨#PCC, -⟩
      wp_auto
      rw [decide_eq_false Hgpnn]
      wp_auto
      cases hcc : pr.cc with
      | none =>
        icases Hccp with %Hccnull
        rw [Hccnull]
        wp_auto
        skip_leaf [hcn, hp, hcc]
      | some cc =>
      iunfold confChangeRO at Hccp
      icases Hccp with ⟨%gcc, #Hgcc, #Hchs, #Hnc⟩
      ihave %Hgccnn := typedPointsto_not_null _ _ _ $$ Hgcc
      icases typedPointsto_split _ _ _ $$ Hgcc with Hgccf
      simp only [TypedPointsto.typedPointstoDef]
      icases Hgccf with ⟨#CChanges, #CNewConf, -⟩
      rw [decide_eq_false Hgccnn]
      wp_auto
      cases hch : cc.changes with
      | none =>
        iunfold optSliceRO at Hchs
        icases Hchs with %Hchnull
        rw [Hchnull]
        wp_auto
        skip_leaf [hcn, hp, hcc, hch]
      | some chs =>
      iunfold optSliceRO at Hchs
      icases Hchs with ⟨%csl, %cvs, #Hcp1, #Hcp2, %Hcvs⟩
      ihave %Hcsl := ownSlice_len $$ Hcp2
      ihave %hnn := typedPointsto_not_null _ _ _ $$ Hcp1
      rw [decide_eq_false hnn]
      wp_auto
      cases chs with
      | nil =>
        have hl0 : ¬ (sint.Z (W64 0) < sint.Z csl.len) := by
          have : cvs = [] := by cases Hcvs; rfl
          subst this; simp at Hcsl; word
        rw [decide_eq_false hl0]
        wp_auto
        skip_leaf [hcn, hp, hcc, hch]
      | cons c cs =>
      cases Hcvs with
      | cons hgc Hrest =>
      rename_i gc gcs
      have hl0 : sint.Z (W64 0) < sint.Z csl.len := by simp at Hcsl; word
      rw [decide_eq_true hl0]
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z csl.len from
        ⟨by word, hl0⟩))]
      wp_apply wp_load_slice_index _ (sint.Z (W64 0)) (gc :: gcs) _ gc (by word) $$ [] as -
      · iframe Hcp2; ipureintro; rfl
      try wp_auto
      rw [decide_strRel hgc.2 (show strRel go!"AddNewServer" "AddNewServer" by strRel_lit)]
      by_cases ha : c.action = "AddNewServer" ∨ c.action = "AddLearner"
      · have hadd : decide (c.action = "AddNewServer") = true ∨
            decide (c.action = "AddNewServer") = false ∧ decide (c.action = "AddLearner") = true := by
          by_cases h1 : c.action = "AddNewServer"
          · exact .inl (decide_eq_true h1)
          · exact .inr ⟨decide_eq_false h1, decide_eq_true (ha.resolve_left h1)⟩
        rcases hadd with h | ⟨h1, h2⟩
        all_goals first
          | (rw [h]; wp_auto)
          | (rw [h1]; wp_auto
             rw [decide_strRel hgc.2 (show strRel go!"AddLearner" "AddLearner" by strRel_lit), h2]; wp_auto)
        all_goals
          wp_apply wp_parseID gc.NID' c.nid $$ [] as %j %okj %Hj
          · ipureintro; exact hgc.1
          cases hpj : parseID c.nid with
          | none => exact absurd ⟨hcn, c, cs, by simp [hp, hcc, hch], ha, hpj⟩ Hbad
          | some jv =>
            rw [hpj] at Hj; obtain ⟨rfl, hjv⟩ := Hj
            try wp_auto
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %sl2 ⟨Hsl2, -⟩
            try wp_auto
            wp_apply wp_slice_append $$ [Hs2 Hscap2 Hsl2] as %s4 ⟨Hs4, Hscap4, -⟩
            · iframe
            try wp_auto
            have ho' : addedServer xl = .ok (some jv) := by
              rcases ha with ha | ha <;> simp [addedServer, hcn, hp, hcc, hch, ha, hpj, Pure.pure, Except.pure]
            rw [ho'] at ho; cases ho
            wp_join_done
            iexists _, _
            iframe
            ipureintro; simp [hjv]
      · have h1 : ¬ c.action = "AddNewServer" := fun h' => ha (.inl h')
        have h2 : ¬ c.action = "AddLearner" := fun h' => ha (.inr h')
        rw [decide_eq_false h1]
        wp_auto
        rw [decide_strRel hgc.2 (show strRel go!"AddLearner" "AddLearner" by strRel_lit), decide_eq_false h2]
        wp_auto
        skip_leaf [hcn, hp, hcc, hch, h1, h2]
    try wp_auto
    wp_for_post
    iframe
    iexists _, _, _, _, ad ++ [o]
    iframe
    ipureintro
    have hm1' : sint.nat (m + W64 1) = sint.nat m + 1 := by clear hmacc hmmem; word
    refine ⟨by clear hmacc hmmem; word, by clear hmacc hmmem; word, ?_, ?_⟩
    · rw [hm1']; exact mapM_take_succ_ok addedServer xs _ xl ad o Hxl hmacc ho
    · intro z
      rw [hm1', Hws3, List.take_add_one, Hxl]
      have := hmmem z
      simp only [List.map_append, List.mem_append, List.filterMap_append, Option.toList_some, List.map_cons,
        List.map_nil, List.mem_cons, List.not_mem_nil, Hlf.1] at this ⊢
      rw [this]; cases o <;> simp <;> grind
  -- the servers
  have hmx : sint.nat m = xs.length := by clear hmacc hmmem; rw [← Hlnl, Hlsl.1]; word
  rw [hmx, List.take_length] at hmacc hmmem
  imod ownSlice_persist $$ Hs with #Hs
  try wp_auto
  wp_apply wp_NewSet ssl ws $$ [] as %srvsl #Hsrv
  · iexact Hs
  rw [SetIds.mk_congr hmmem]
  try wp_auto
  generalize hsrvd : SetIds.mk (List.map Line.nid xs ++ List.filterMap id ad) = srv
  ihave #Hsrv0 := Hsrv
  iunfold setRO at Hsrv0
  icases Hsrv0 with ⟨%sxs, #Hsxs, %Hsxsm⟩
  ihave %Hsxsl := ownSlice_len $$ Hsxs
  wp_apply wp_slice_make2 (V := Bool) lsl.len $$ [] as %bsl ⟨Hbs, Hbcap⟩
  · ipureintro; exact Hlsl.2
  try wp_auto
  wp_apply wp_map_make1 (K := w64) (V := w64) as %lm Hlm
  try wp_auto
  rename_i ivar_ptr
  irename : (ivar_ptr ↦ (zero_val w64) : IProp GF) => ivar
  ipersist t
  ipersist lines
  ipersist Server
  ipersist bootstrap
  ipersist last
  ipersist isBootstrapName
  ihave IHb : iprop(∃ (n iv : w64) (bs : List Bool) (mm : GMap w64 w64),
      "i" ∷ i_ptr ↦ n ∗ "ivar" ∷ ivar_ptr ↦ iv ∗ "Hbs" ∷ bsl ↦* bs ∗ "Hlm" ∷ lm ↦$ mm ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z srvsl.len ∧
        bs = (List.range xs.length).map
          (fun k => (srv.take (sint.nat n)).any (fun j => (bootstrapOf xs j).1.getD k false)) ∧
        (∀ j ∈ srv.take (sint.nat n), (bootstrapOf xs j).2 ≠ 0) ∧
        (∀ w : w64, (mm !! w).isSome → uint.nat w ∈ srv.take (sint.nat n)) ∧
        (∀ w : w64, uint.nat w ∈ srv.take (sint.nat n) →
          sint.Z ((mm !! w).getD (W64 0)) = ((bootstrapOf xs (uint.nat w)).2 : Int))⌝)
      $$ [i ivar Hbs Hlm]
  · iexists _, _, _, _
    iframe
    ipureintro
    refine ⟨by word, by word, ?_, ?_, ?_, ?_⟩
    · rw [show sint.nat (W64 0) = 0 from rfl]
      rw [← Hlnl, Hlsl.1]
      apply List.ext_getElem <;> simp; intros; rfl
    · rw [show sint.nat (W64 0) = 0 from rfl]; simp
    · intro w h; simp at h
    · rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for IHb
  obtain ⟨hb0, hb1, hbs, hbnz, hbkeys, hbval⟩ := Hn
  wp_if_destruct
  · have Hnlt2 : sint.Z n < sint.Z srvsl.len := Hif
    have Hlt : sint.nat n < sxs.length := by rw [Hsxsl.1]; word
    obtain ⟨iw, Hiw⟩ : ∃ v, sxs[sint.nat n]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hsi : srv[sint.nat n]? = some (uint.nat iw) := by rw [← Hsxsm, List.getElem?_map, Hiw]; rfl
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z srvsl.len from ⟨hb0, Hnlt2⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) sxs _ iw hb0 $$ [] as -
    · iframe Hsxs; ipureintro; exact Hiw
    try wp_auto
    ihave IHf : iprop(∃ (lv fv fnv : w64),
        "l" ∷ l_ptr ↦ lv ∗ "first" ∷ first_ptr ↦ fv ∗ "firstNon" ∷ firstNon_ptr ↦ fnv ∗
        "ivar" ∷ ivar_ptr ↦ iw ∗
        "%Hl" ∷ ⌜1 ≤ sint.Z lv ∧ sint.Z lv ≤ (xs.length : Int) + 1 ∧
          sint.Z fv = ((((((bIdx xs).take (sint.nat lv - 1)).find?
            (fun p => p.2.nid == uint.nat iw && isBootstrapName p.2.ev.name)).map Prod.fst).getD 0 : Nat) : Int) ∧
          sint.Z fnv = ((((((bIdx xs).take (sint.nat lv - 1)).find?
            (fun p => p.2.nid == uint.nat iw && !isBootstrapName p.2.ev.name)).map Prod.fst).getD 0 : Nat) : Int)⌝)
        $$ [l first firstNon ivar]
    · iexists _, _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_, ?_⟩ <;> rw [show sint.nat (W64 1) - 1 = 0 from rfl] <;> simp
    wp_for IHf
    obtain ⟨hl1, hl2, hfv, hfnv⟩ := Hl
    wp_if_destruct
    · have hlle : sint.Z lv ≤ sint.Z lsl.len := Hif
      have hj : sint.nat lv - 1 < xs.length := by rw [← Hlnl, Hlsl.1]; clear hfv hfnv; word
      obtain ⟨lg, Hlg⟩ : ∃ v, lns[sint.nat lv - 1]? = some v :=
        ⟨_, List.getElem?_eq_getElem (by rw [Hlnl]; exact hj)⟩
      obtain ⟨xl, Hxl⟩ : ∃ v, xs[sint.nat lv - 1]? = some v := ⟨_, List.getElem?_eq_getElem hj⟩
      have hxlg : xs.getD (sint.nat lv - 1) default = xl := by simp [List.getD_eq_getElem?_getD, Hxl]
      ihave #Hlgx := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => lineRO (GF := GF) a b) Hlg Hxl $$ Hlr
      ihave #Hlgx0 := Hlgx
      iunfold lineRO at Hlgx0
      icases Hlgx0 with ⟨⟨%ge, #Hgev, #Hger⟩, %Hlf, -⟩
      iunfold eventRO at Hger
      icases Hger with ⟨%Hef2, -⟩
      icases typedPointsto_split _ _ _ $$ Hgev with Hgevf
      simp only [TypedPointsto.typedPointstoDef]
      icases Hgevf with ⟨#GName, -⟩
      have hidx : sint.Z (lv - W64 1) = ((sint.nat lv - 1 : Nat) : Int) := by clear hfv hfnv; word
      have hlv1 : sint.nat (lv + W64 1) = sint.nat lv + 1 := by
        have : (xs.length : Int) < 2 ^ 40 := by rw [hxl]; exact Hb.2
        clear hfv hfnv; word
      have hjs : sint.nat (lv + W64 1) - 1 = (sint.nat lv - 1) + 1 := by
        have : 1 ≤ sint.nat lv := by clear hfv hfnv; word
        omega
      try wp_auto
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (lv - W64 1) ∧ sint.Z (lv - W64 1) < sint.Z lsl.len by
        clear hfv hfnv; word))]
      wp_apply wp_load_slice_index _ (sint.Z (lv - W64 1)) lns _ lg (by clear hfv hfnv; word) $$ [] as -
      · iframe Hl; ipureintro; rw [hidx, Int.toNat_natCast]; exact Hlg
      try wp_auto
      have hid : (lg.nid' = iw) ↔ xl.nid = uint.nat iw := by rw [id_eq_iff, Hlf.1]
      by_cases hni : ¬ xl.nid = uint.nat iw
      · rw [decide_eq_false (fun h => hni (hid.1 h))]
        wp_auto
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        ipureintro
        refine ⟨by clear hfv hfnv; word, by clear hfv hfnv; word, ?_, ?_⟩
        · rw [hjs, find_fst_step _ xs _ hj, hxlg]; simp [hni, hfv]
        · rw [hjs, find_fst_step _ xs _ hj, hxlg]; simp [hni, hfnv]
      replace hni : xl.nid = uint.nat iw := Classical.not_not.mp hni
      rw [decide_eq_true (hid.2 hni)]
      wp_auto
      have hlvj : sint.Z lv = ((sint.nat lv - 1 + 1 : Nat) : Int) := by clear hfv hfnv; word
      wp_join iprop(∃ fv' : w64, "first" ∷ first_ptr ↦ fv' ∗ "ln" ∷ ln_ptr ↦ lg ∗ "l" ∷ l_ptr ↦ lv ∗
          "%Hfv'" ∷ ⌜sint.Z fv' = ((((((bIdx xs).take (sint.nat lv - 1 + 1)).find?
            (fun p => p.2.nid == uint.nat iw && isBootstrapName p.2.ev.name)).map Prod.fst).getD 0 : Nat) : Int)⌝)
        at next with [first ln l] as ⟨%fv', first, ln, l, %Hfv'⟩
      · rw [find_fst_step _ xs _ hj, hxlg]
        by_cases hf0 : fv = W64 0
        · have hold : (((((bIdx xs).take (sint.nat lv - 1)).find?
              (fun p => p.2.nid == uint.nat iw && isBootstrapName p.2.ev.name)).map Prod.fst).getD 0) = 0 := by
            rw [hf0] at hfv; clear hfnv; simp at hfv; omega
          rw [decide_eq_true hf0]
          wp_auto
          isbn_eval Hef2.1, xl.ev.name
          all_goals
            wp_join_done
            iexists _
            iframe
            ipureintro
            simp only [hold, hni, hb, beq_self_eq_true, Bool.true_and, true_and]
            simp
            first | exact hlvj | (rw [hf0]; rfl)
        · rw [decide_eq_false hf0]
          wp_auto
          wp_join_done
          iexists _
          iframe
          ipureintro
          have hold : (((((bIdx xs).take (sint.nat lv - 1)).find?
              (fun p => p.2.nid == uint.nat iw && isBootstrapName p.2.ev.name)).map Prod.fst).getD 0) ≠ 0 := by
            intro h; rw [h] at hfv; apply hf0; clear hfnv; simp at hfv; word
          simp only [hold, _root_.false_and, ite_false]
          exact hfv
      wp_join iprop(∃ fnv' : w64, "firstNon" ∷ firstNon_ptr ↦ fnv' ∗ "l" ∷ l_ptr ↦ lv ∗
          "%Hfnv'" ∷ ⌜sint.Z fnv' = ((((((bIdx xs).take (sint.nat lv - 1 + 1)).find?
            (fun p => p.2.nid == uint.nat iw && !isBootstrapName p.2.ev.name)).map Prod.fst).getD 0 : Nat) : Int)⌝)
        at (if: _ then _ else _) with [firstNon ln l] as ⟨%fnv', firstNon, l, %Hfnv'⟩
      · rw [find_fst_step _ xs _ hj, hxlg]
        by_cases hf0 : fnv = W64 0
        · have hold : (((((bIdx xs).take (sint.nat lv - 1)).find?
              (fun p => p.2.nid == uint.nat iw && !isBootstrapName p.2.ev.name)).map Prod.fst).getD 0) = 0 := by
            rw [hf0] at hfnv; clear hfv Hfv'; simp at hfnv; omega
          rw [decide_eq_true hf0]
          wp_auto
          isbn_eval Hef2.1, xl.ev.name
          all_goals
            wp_join_done
            iexists _
            iframe
            ipureintro
            simp only [hold, hni, hb, beq_self_eq_true, Bool.true_and, true_and]
            simp
            first | exact hlvj | (rw [hf0]; rfl)
        · rw [decide_eq_false hf0]
          wp_auto
          wp_join_done
          iexists _
          iframe
          ipureintro
          have hold : (((((bIdx xs).take (sint.nat lv - 1)).find?
              (fun p => p.2.nid == uint.nat iw && !isBootstrapName p.2.ev.name)).map Prod.fst).getD 0) ≠ 0 := by
            intro h; rw [h] at hfnv; apply hf0; clear hfv Hfv'; simp at hfnv; word
          simp only [hold, _root_.false_and, ite_false]
          exact hfnv
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨by clear hfv hfnv Hfv' Hfnv'; word, by clear hfv hfnv Hfv' Hfnv'; word, ?_, ?_⟩
      · rw [hjs]; exact Hfv'
      · rw [hjs]; exact Hfnv'
    have hlvx : sint.nat lv - 1 = xs.length := by
      have := Hlsl.1; rw [Hlnl] at this; clear hfv hfnv; word
    rw [hlvx, ← bFirst_full] at hfv
    rw [hlvx, ← bFirstNon_full] at hfnv
    try wp_auto
    have hxlen : sint.Z lsl.len = (xs.length : Int) := by rw [← Hlnl, Hlsl.1]; word
    wp_join iprop(∃ uv : w64, "upper" ∷ upper_ptr ↦ uv ∗ "%Huv" ∷ ⌜sint.Z uv = (bUpper xs (uint.nat iw) : Int)⌝)
      at next with [upper firstNon] as ⟨%uv, upper, %Huv⟩
    · by_cases hf0 : fnv = W64 0
      · rw [decide_eq_true hf0]
        wp_auto
        wp_join_done
        iexists _
        iframe
        ipureintro
        have : bFirstNon xs (uint.nat iw) = 0 := by rw [hf0] at hfnv; simp at hfnv; omega
        simp [bUpper, this, hxlen]
      · rw [decide_eq_false hf0]
        wp_auto
        wp_join_done
        iexists _
        iframe
        ipureintro
        have h1 : bFirstNon xs (uint.nat iw) ≠ 0 := by
          intro h; rw [h] at hfnv; apply hf0; simp at hfnv; word
        have h2 := bFirstNon_le xs (uint.nat iw)
        have : (bFirstNon xs (uint.nat iw) : Int) < 2 ^ 40 := by have := Hb.2; rw [← hxl] at this; unfold numBound at this; omega
        simp only [bUpper, bne_iff_ne, ne_eq, h1, not_false_eq_true, ite_true]
        rw [show ((bFirstNon xs (uint.nat iw) - 1 : Nat) : Int) = (bFirstNon xs (uint.nat iw) : Int) - 1 by omega]
        word
    wp_func_call
    wp_call
    try wp_auto
    wp_join (v := #(if sint.Z (W64 1) < sint.Z fv then fv else W64 1)) iprop(True)
      at (if: _ then _ else _) with [] as -
    · by_cases hmx : sint.Z (W64 1) < sint.Z fv
      · rw [decide_eq_true hmx]; wp_auto; rw [ite_cond_eq_true _ _ (eq_true hmx)]; wp_join_done; try (ipureintro; trivial)
      · rw [decide_eq_false hmx]; wp_auto; rw [ite_eq_right_iff.2 (fun h => absurd h hmx)]; wp_join_done
        try (ipureintro; trivial)
    have hk0 : sint.Z (if sint.Z (W64 1) < sint.Z fv then fv else W64 1) = ((max (bFirst xs (uint.nat iw)) 1 : Nat) : Int) := by
      split <;> rename_i h <;> rw [hfv] at h <;> (try rw [hfv]) <;> simp at h ⊢ <;> omega
    generalize hk0d : (if sint.Z (W64 1) < sint.Z fv then fv else W64 1) = k0w at hk0
    try wp_auto
    have hsnd : srv.Nodup := by rw [← hsrvd]; exact SetIds.mk_nodup _
    have hinot : uint.nat iw ∉ srv.take (sint.nat n) := nodup_not_mem_take hsnd Hsi
    have hmmi : mm !! iw = none := by
      cases h : mm !! iw with
      | none => rfl
      | some _ => exact absurd (hbkeys iw (by simp [h])) hinot
    have hxb : (xs.length : Int) < 2 ^ 40 := by rw [hxl]; exact Hb.2
    have hub := bUpper_le xs (uint.nat iw)
    have hfb := bFirst_le xs (uint.nat iw)
    ihave IHk : iprop(∃ (kv : w64) (bs' : List Bool) (mm' : GMap w64 w64),
        "k" ∷ k_ptr ↦ kv ∗ "Hbs" ∷ bsl ↦* bs' ∗ "Hlm" ∷ lm ↦$ mm' ∗ "ivar" ∷ ivar_ptr ↦ iw ∗
        "upper" ∷ upper_ptr ↦ uv ∗
        "%Hk" ∷ ⌜((max (bFirst xs (uint.nat iw)) 1 : Nat) : Int) ≤ sint.Z kv ∧
          sint.Z kv ≤ max ((max (bFirst xs (uint.nat iw)) 1 : Nat) : Int) ((bUpper xs (uint.nat iw) : Int) + 1) ∧
          bs' = bootFlags xs srv (sint.nat n) (uint.nat iw) (sint.nat kv) ∧
          (∀ w, w ≠ iw → mm' !! w = mm !! w) ∧
          sint.Z ((mm' !! iw).getD (W64 0)) =
            ((((bIdx xs).take (sint.nat kv - 1)).foldl (bLastF xs (uint.nat iw)) 0 : Nat) : Int)⌝)
      $$ [k Hbs Hlm ivar upper]
    · iexists _, _, _
      iframe
      ipureintro
      have hk0n : sint.nat k0w = max (bFirst xs (uint.nat iw)) 1 := by rw [show sint.nat k0w = (sint.Z k0w).toNat from rfl, hk0]; simp
      refine ⟨by rw [hk0]; exact Int.le_refl _, by rw [hk0]; omega, ?_, fun _ _ => rfl, ?_⟩
      · rw [hk0n, bootFlags_init, hbs]
      · rw [hmmi, hk0n, last_init]; rfl
    wp_for IHk
    obtain ⟨hk1, hk2, hbs', hmm1, hmm2⟩ := Hk
    wp_if_destruct
    · have hkv : sint.Z kv ≤ (bUpper xs (uint.nat iw) : Int) := by rw [← Huv]; exact Hif
      have hkpos : 1 ≤ sint.Z kv := by omega
      have hj : sint.nat kv - 1 < xs.length := by clear hbs' hmm2; word
      have hkn1 : sint.nat (kv + W64 1) = sint.nat kv + 1 := by clear hbs' hmm2; word
      have hidx : sint.Z (kv - W64 1) = ((sint.nat kv - 1 : Nat) : Int) := by clear hbs' hmm2; word
      have hkn : sint.Z kv = ((sint.nat kv : Nat) : Int) := by clear hbs' hmm2; word
      obtain ⟨lg, Hlg⟩ : ∃ v, lns[sint.nat kv - 1]? = some v :=
        ⟨_, List.getElem?_eq_getElem (by rw [Hlnl]; exact hj)⟩
      obtain ⟨xl, Hxl⟩ : ∃ v, xs[sint.nat kv - 1]? = some v := ⟨_, List.getElem?_eq_getElem hj⟩
      have hxlg : xs.getD (sint.nat kv - 1) default = xl := by simp [List.getD_eq_getElem?_getD, Hxl]
      ihave #Hlgx := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => lineRO (GF := GF) a b) Hlg Hxl $$ Hlr
      ihave #Hlgx0 := Hlgx
      iunfold lineRO at Hlgx0
      icases Hlgx0 with ⟨-, %Hlf, -⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (kv - W64 1) ∧ sint.Z (kv - W64 1) < sint.Z lsl.len by
        rw [hidx, hxlen]; omega))]
      icases ownSlice_elem_acc (sint.Z (kv - W64 1)) lg lsl _ lns (by rw [hidx]; omega)
        (by rw [hidx, Int.toNat_natCast]; exact Hlg) $$ Hl with ⟨#Hel, -⟩
      icases typedPointsto_split _ _ _ $$ Hel with Helf
      simp only [TypedPointsto.typedPointstoDef]
      icases Helf with ⟨-, #Lnid, -⟩
      wp_auto
      have hid : (lg.nid' = iw) ↔ xl.nid = uint.nat iw := by rw [id_eq_iff, Hlf.1]
      have hk1' := hk1
      rw [hkn] at hk1'
      have hkv' := hkv
      rw [hkn] at hkv'
      by_cases hni : ¬ xl.nid = uint.nat iw
      · rw [decide_eq_false (fun h => hni (hid.1 h))]
        wp_auto
        wp_for_post
        iframe
        iexists _, _, _
        iframe
        ipureintro
        refine ⟨by clear hbs' hmm2; word, by clear hbs' hmm2; word, ?_, hmm1, ?_⟩
        · rw [hkn1, hbs', bootFlags_skip xs srv _ _ _ (by omega) (by omega)]
          rw [show sint.nat kv - 1 = sint.nat kv - 1 from rfl, hxlg]; exact hni
        · rw [hmm2, hkn1, show sint.nat kv + 1 - 1 = (sint.nat kv - 1) + 1 by omega,
            last_step xs _ _ hj (by omega) (by omega), hxlg]
          simp [hni]
      replace hni : xl.nid = uint.nat iw := Classical.not_not.mp hni
      rw [decide_eq_true (hid.2 hni)]
      wp_auto
      ihave %Hbsl := ownSlice_len $$ Hbs
      have hbsl : bs'.length = xs.length := by rw [hbs']; simp [bootFlags]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (kv - W64 1) ∧ sint.Z (kv - W64 1) < sint.Z bsl.len by
        rw [hidx]; have := Hbsl.1; rw [hbsl] at this; clear hbs' hmm2; word))]
      wp_apply wp_store_slice_index bsl (sint.Z (kv - W64 1)) bs' true $$ [Hbs] as Hbs
      · iframe Hbs; ipureintro; rw [hidx, hbsl]; omega
      try wp_auto
      wp_apply wp_mapInsert $$ [Hlm] as Hlm
      · iexact Hlm
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _
      iframe
      ipureintro
      refine ⟨by clear hbs' hmm2; word, by clear hbs' hmm2; word, ?_, ?_, ?_⟩
      · rw [hidx, Int.toNat_natCast, hkn1, hbs']
        exact bootFlags_set xs srv _ _ _ (by omega) (by omega) (by omega) (by omega) (by rw [hxlg]; exact hni)
      · intro w hw; rw [GMap.lookup_insert_ne _ _ (Ne.symm hw)]; exact hmm1 w hw
      · rw [GMap.lookup_insert, hkn1, show sint.nat kv + 1 - 1 = (sint.nat kv - 1) + 1 by omega,
          last_step xs _ _ hj (by omega) (by omega), hxlg]
        simp only [Option.getD_some, hni, beq_self_eq_true, ite_true]
        rw [show sint.nat kv - 1 + 1 = sint.nat kv by omega]; exact hkn
    have hkgt : (bUpper xs (uint.nat iw) : Int) < sint.Z kv := by rw [← Huv]; omega
    have hkn : sint.Z kv = ((sint.nat kv : Nat) : Int) := by clear hbs' hmm2; word
    have hkgt' : bUpper xs (uint.nat iw) < sint.nat kv := by omega
    have hlast : sint.Z ((mm' !! iw).getD (W64 0)) = ((bootstrapOf xs (uint.nat iw)).2 : Int) := by
      rw [hmm2, bootstrapOf_eq, last_end xs _ (sint.nat kv) hkgt']
    have hbsn := bootFlags_end xs srv (sint.nat n) (uint.nat iw) (sint.nat kv) hkgt' Hsi
    rw [hbsn] at hbs'
    wp_apply wp_map_lookup1 $$ [Hlm] as Hlm
    · iexact Hlm
    rw [show (zero_val w64) = W64 0 from rfl]
    have himem : uint.nat iw ∈ srv := List.mem_of_getElem? Hsi
    by_cases h0 : (bootstrapOf xs (uint.nat iw)).2 = 0
    · have : (mm' !! iw).getD (W64 0) = W64 0 := by rw [h0] at hlast; clear hbs' hmm2; word
      rw [this]
      try wp_auto
      loop_fail (boot_err pv cq hne hacc hmacc (by rw [hsrvd]; exact himem) h0)
    have : (mm' !! iw).getD (W64 0) ≠ W64 0 := by
      intro h; rw [h] at hlast; apply h0; simp at hlast; omega
    try wp_auto
    rw [decide_eq_false this]
    wp_auto
    wp_for_post
    iframe
    iexists _, _, _, _
    iframe
    ipureintro
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by clear hbs' hmm2 hbs; word
    have htk : srv.take (sint.nat n + 1) = srv.take (sint.nat n) ++ [uint.nat iw] := by
      rw [List.take_add_one, Hsi]; rfl
    refine ⟨by clear hbs' hmm2 hbs; word, by clear hbs' hmm2 hbs; word, ?_, ?_, ?_, ?_⟩
    · rw [hn1]; exact hbs'
    · rw [hn1, htk]; intro j hj
      rcases List.mem_append.1 hj with hj | hj
      · exact hbnz j hj
      · rw [List.mem_singleton] at hj; subst hj; exact h0
    · rw [hn1, htk]; intro w hw
      by_cases hwi : w = iw
      · subst hwi; simp
      · rw [hmm1 w hwi] at hw; exact List.mem_append_left _ (hbkeys w hw)
    · rw [hn1, htk]; intro w hw
      by_cases hwi : w = iw
      · subst hwi; exact hlast
      · rw [hmm1 w hwi]
        rcases List.mem_append.1 hw with hw | hw
        · exact hbval w hw
        · rw [List.mem_singleton] at hw; exact absurd ((id_eq_iff _ _).2 hw) hwi
  -- the bootstrap flags and last bootstrap lines
  have hnsrv : sint.nat n = srv.length := by rw [← Hsxsm, List.length_map, Hsxsl.1]; word
  rw [hnsrv, List.take_length] at hbs hbnz hbkeys hbval
  try wp_auto
  ipersist bootstrappedConfig
  ipersist bootstrapConfs
  wp_join (Q := fun v => iprop(∃ (cs : GoSlice) (e : GoInterface), ⌜v = PairV #cs #e⌝ ∗ "Hlm" ∷ lm ↦$ mm ∗
      match tBC xs (bootstrapOf xs (xs.getD 0 default).nid).2 with
      | .ok c => ⌜e = interface.nil⌝ ∗ setRO cs c
      | .error _ => ⌜e ≠ interface.nil⌝))
    at (Let "$a0" _ (App (App (Val (GoInstruction (GoLoad _))) (Val #bootstrappedConfig_ptr)) _)) with [Hlm]
  · have hxpos : 0 < xs.length := by rw [hxl]; exact List.length_pos_iff.2 hne
    obtain ⟨lg0, Hlg0⟩ : ∃ v, lns[0]? = some v := ⟨_, List.getElem?_eq_getElem (by rw [Hlnl]; exact hxpos)⟩
    obtain ⟨x0, Hx0⟩ : ∃ v, xs[0]? = some v := ⟨_, List.getElem?_eq_getElem hxpos⟩
    have hx0 : xs.getD 0 default = x0 := by rw [List.getD_eq_getElem?_getD, Hx0]; rfl
    have hxlen : sint.Z lsl.len = (xs.length : Int) := by rw [← Hlnl, Hlsl.1]; word
    ihave #Hl0 := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => lineRO (GF := GF) a b) Hlg0 Hx0 $$ Hlr
    ihave #Hl00 := Hl0
    iunfold lineRO at Hl00
    icases Hl00 with ⟨-, %Hlf0, -⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z lsl.len by
      rw [hxlen]; simp; omega))]
    icases ownSlice_elem_acc (sint.Z (W64 0)) lg0 lsl _ lns (by simp) (by simpa using Hlg0) $$ Hl with ⟨#Hel0, -⟩
    icases typedPointsto_split _ _ _ $$ Hel0 with Hel0f
    simp only [TypedPointsto.typedPointstoDef]
    icases Hel0f with ⟨-, #L0nid, -⟩
    have hn0srv : x0.nid ∈ srv := by
      rw [← hsrvd, SetIds.mem_mk]; exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_of_getElem? Hx0))
    rw [hx0]
    wp_auto
    have hjsrv : uint.nat lg0.nid' ∈ srv := by rw [Hlf0.1]; exact hn0srv
    have hL := hbval lg0.nid' hjsrv
    have hL0 := hbnz _ hjsrv
    have hLle := bootstrapOf_snd_le xs (uint.nat lg0.nid')
    rw [Hlf0.1] at hL hL0 hLle
    wp_apply wp_map_lookup1 $$ [Hlm] as Hlm
    · iexact Hlm
    rw [show (zero_val w64) = W64 0 from rfl]
    generalize (mm !! lg0.nid').getD (W64 0) = lw at hL
    generalize (bootstrapOf xs x0.nid).2 = L at hL hL0 hLle ⊢
    have hxb : (xs.length : Int) < 2 ^ 40 := by rw [hxl]; exact Hb.2
    have hidxL : sint.Z (lw - W64 1) = ((L - 1 : Nat) : Int) := by
      have : 1 ≤ L := Nat.pos_of_ne_zero hL0
      rw [show ((L - 1 : Nat) : Int) = (L : Int) - 1 by omega, ← hL]; word
    try wp_auto
    have hLlt : L - 1 < xs.length := by omega
    obtain ⟨lgL, HlgL⟩ : ∃ v, lns[L - 1]? = some v := ⟨_, List.getElem?_eq_getElem (by rw [Hlnl]; exact hLlt)⟩
    obtain ⟨xL, HxL⟩ : ∃ v, xs[L - 1]? = some v := ⟨_, List.getElem?_eq_getElem hLlt⟩
    have hxL : xs.getD (L - 1) default = xL := by rw [List.getD_eq_getElem?_getD, HxL]; rfl
    ihave #HlL := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => lineRO (GF := GF) a b) HlgL HxL $$ Hlr
    ihave #HlL0 := HlL
    iunfold lineRO at HlL0
    icases HlL0 with ⟨⟨%geL, #HgevL, #HgerL⟩, %HlfL, %laL, %lbL, %HlabL, #HcL0, #HcL1⟩
    iunfold eventRO at HgerL
    icases HgerL with ⟨%HefL, -, -, #HepropL⟩
    icases typedPointsto_split _ _ _ $$ HgevL with HgevLf
    simp only [TypedPointsto.typedPointstoDef]
    icases HgevLf with ⟨#GLName, -, -, -, -, -, -, #GLProp, -⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (lw - W64 1) ∧ sint.Z (lw - W64 1) < sint.Z lsl.len by
      rw [hidxL, hxlen]; omega))]
    wp_apply wp_load_slice_index _ (sint.Z (lw - W64 1)) lns _ lgL (by rw [hidxL]; omega) $$ [] as -
    · iframe Hl; ipureintro; rw [hidxL, Int.toNat_natCast]; exact HlgL
    try wp_auto
    simp only [tBC, hxL]
    rw [decide_strRel HefL.1 (show strRel go!"ApplyConfChange" "ApplyConfChange" by strRel_lit)]
    by_cases hac : xL.ev.name = "ApplyConfChange"
    · rw [decide_eq_true hac]
      wp_auto
      cases hp : xL.ev.prop with
      | none =>
        iunfold propsRO at HepropL
        icases HepropL with %Hpnull
        rw [Hpnull]
        wp_auto
        bc_fail [hac, hp]
      | some pr =>
      iunfold propsRO at HepropL
      icases HepropL with ⟨%gp, #Hgp, #Hccp⟩
      ihave %Hgpnn := typedPointsto_not_null _ _ _ $$ Hgp
      icases typedPointsto_split _ _ _ $$ Hgp with Hgpf
      simp only [TypedPointsto.typedPointstoDef]
      icases Hgpf with ⟨#PCC, -⟩
      rw [decide_eq_false Hgpnn]
      wp_auto
      cases hcc : pr.cc with
      | none =>
        icases Hccp with %Hccnull
        rw [Hccnull]
        wp_auto
        bc_fail [hac, hp, hcc]
      | some cc =>
      iunfold confChangeRO at Hccp
      icases Hccp with ⟨%gcc, #Hgcc, -, #Hnc⟩
      ihave %Hgccnn := typedPointsto_not_null _ _ _ $$ Hgcc
      icases typedPointsto_split _ _ _ $$ Hgcc with Hgccf
      simp only [TypedPointsto.typedPointstoDef]
      icases Hgccf with ⟨-, #CNewConf, -⟩
      rw [decide_eq_false Hgccnn]
      wp_auto
      cases hnc : cc.newconf with
      | none =>
        iunfold optSliceRO at Hnc
        icases Hnc with %Hncnull
        rw [Hncnull]
        wp_auto
        bc_fail [hac, hp, hcc, hnc]
      | some nc =>
      iunfold optSliceRO at Hnc
      icases Hnc with ⟨%ncsl, %ncvs, #Hncp, #Hncs, %Hncr⟩
      ihave %Hncnn := typedPointsto_not_null _ _ _ $$ Hncp
      rw [decide_eq_false Hncnn]
      wp_auto
      wp_apply wp_toSet ncsl _ ncvs nc $$ [] as %cset %okc ⟨-, Hcset⟩
      · iframe Hncs; ipureintro; exact Hncr
      try wp_auto
      cases htc : toSet nc with
      | none =>
        simp only [htc]
        icases Hcset with %Hokc
        subst Hokc
        wp_auto
        bc_fail [hac, hp, hcc, hnc, htc]
      | some c =>
      simp only [htc]
      icases Hcset with ⟨%Hokc, #Hcs⟩
      subst Hokc
      wp_auto
      iexists _, _
      iframe Hlm
      isplitl []
      · ipureintro; rfl
      simp [hac, hp, hcc, hnc, htc, Pure.pure, Except.pure]
      isplitl []
      · ipureintro; trivial
      iexact Hcs
    rw [decide_eq_false hac]
    wp_auto
    icases typedPointsto_split _ _ _ $$ ln with Hlnf
    simp only [TypedPointsto.typedPointstoDef]
    icases Hlnf with ⟨-, -, -, -, Lconf, -⟩
    icases array_acc _ 0 _ _ _ laL (Int.le_refl _) (by rw [HlabL]; rfl) $$ Lconf with ⟨Hc0p, -⟩
    rw [show sint.Z (W64 0) = 0 from rfl]
    wp_auto
    iexists _, _
    iframe Hlm
    isplitl []
    · ipureintro; rfl
    have : (xL.ev.name == "ApplyConfChange") = false := by simpa using hac
    simp only [this, Bool.false_eq_true, ite_false, Pure.pure, Except.pure]
    isplitl []
    · ipureintro; trivial
    iexact HcL0
  iintro ⟨%cs, %e, %Hv, Hlm, Hbc⟩
  subst Hv
  have hxpos : 0 < xs.length := by rw [hxl]; exact List.length_pos_iff.2 hne
  have hx0srv : (xs.getD 0 default).nid ∈ srv := by
    rw [← hsrvd, SetIds.mem_mk]
    exact List.mem_append_left _ (List.mem_map_of_mem (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hxpos]; exact List.getElem_mem hxpos))
  have htail := newTraceWith_tail pv cq hne hacc hmacc
  rw [hsrvd] at htail
  try wp_auto
  cases hbc : tBC xs (bootstrapOf xs (xs.getD 0 default).nid).2 with
  | error eb =>
    icases Hbc with %He
    cases e with
    | nil => exact absurd rfl He
    | ok ei =>
    wp_auto
    iapply HΦ
    rw [htail, tail_init_err pv cq hbnz hx0srv hbc]
    ipureintro; exact He
  | ok c0 =>
  icases Hbc with ⟨%He, #Hc0⟩
  subst He
  try wp_auto
  ipersist InitSrv
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Set.TypeAssumptions.ptr_Subset_unfold.method_unfold]
  try wp_auto
  wp_apply wp_Subset cs c0 srvsl srv $$ []
  · iframe Hc0 Hsrv
  cases hsub : c0.subset srv
  · try wp_auto
    wp_apply wp_traceError as %e %He
    try wp_auto
    iapply HΦ
    obtain ⟨e', he'⟩ := tail_sub_err pv cq hbnz hx0srv hbc hsub
    rw [htail, he']
    ipureintro; exact He
  try wp_auto
  generalize «$r0_ptr» = tp at Hr0nn ⊢
  wp_apply wp_map_make1 (K := w64) (V := Loc) as %smap Hsm
  try wp_auto
  rename_i iv2_ptr
  irename : (iv2_ptr ↦ (zero_val w64) : IProp GF) => ivar
  generalize «$r0_ptr» = sp
  ipersist «$r0»
  ipersist s
  imod ownSlice_persist $$ Hbs with #Hbs
  ihave IHs : iprop(∃ (n iv : w64) (sm : GMap w64 Loc) (cfgsP : List (ID × SetIds))
        (bconfsP : List (ID × List SetIds)),
      "i" ∷ i_ptr ↦ n ∗ "ivar" ∷ iv2_ptr ↦ iv ∗ "Hsm" ∷ smap ↦$ sm ∗ "Hlm" ∷ lm ↦$ mm ∗
      "Hsrvs" ∷ ([∗list] j ∈ srv.take (sint.nat n), ∃ q : Loc, ⌜sm !! (W64 (Int.ofNat j)) = some q⌝ ∗
        serverRO q (tServerOf xs srv cfgsP bconfsP j)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z srvsl.len ∧
        (srv.take (sint.nat n)).mapM (tCfgF xs srv) = .ok cfgsP ∧
        (srv.take (sint.nat n)).mapM (tBconfF xs srv) = .ok bconfsP ∧
        ∀ k : w64, (sm !! k).isSome ↔ uint.nat k ∈ srv.take (sint.nat n)⌝)
      $$ [i ivar Hsm Hlm]
  · iexists _, _, _, [], []
    iframe
    isplitl []
    · rw [show sint.nat (W64 0) = 0 from rfl]; simp; iempintro
    ipureintro
    refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; rfl,
      by rw [show sint.nat (W64 0) = 0 from rfl]; rfl, ?_⟩
    intro k; rw [show sint.nat (W64 0) = 0 from rfl]; simp
  wp_for IHs
  obtain ⟨hs0, hs1, hcfP, hbfP, hsmk⟩ := Hn
  have hxb : (xs.length : Int) < 2 ^ 40 := by rw [hxl]; exact Hb.2
  have hxlen : sint.Z lsl.len = (xs.length : Int) := by rw [← Hlnl, Hlsl.1]; word
  wp_if_destruct
  · have Hnlt2 : sint.Z n < sint.Z srvsl.len := Hif
    have Hlt : sint.nat n < sxs.length := by rw [Hsxsl.1]; word
    obtain ⟨iw, Hiw⟩ : ∃ v, sxs[sint.nat n]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hsi : srv[sint.nat n]? = some (uint.nat iw) := by rw [← Hsxsm, List.getElem?_map, Hiw]; rfl
    have himem : uint.nat iw ∈ srv := List.mem_of_getElem? Hsi
    have hsnd : srv.Nodup := by rw [← hsrvd]; exact SetIds.mk_nodup _
    have hinot : uint.nat iw ∉ srv.take (sint.nat n) := nodup_not_mem_take hsnd Hsi
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z srvsl.len from ⟨hs0, Hnlt2⟩))]
    wp_apply wp_load_slice_index _ (sint.Z n) sxs _ iw hs0 $$ [] as -
    · iframe Hsxs; ipureintro; exact Hiw
    try wp_auto
    have hL := hbval iw himem
    have hL0 := hbnz _ himem
    have hLle := bootstrapOf_snd_le xs (uint.nat iw)
    wp_apply wp_map_lookup1 $$ [Hlm] as Hlm
    · iexact Hlm
    rw [show (zero_val w64) = W64 0 from rfl]
    generalize hlwd : (mm !! iw).getD (W64 0) = lw at hL
    generalize hLd : (bootstrapOf xs (uint.nat iw)).2 = L at hL hL0 hLle
    have hidxL : sint.Z (lw - W64 1) = ((L - 1 : Nat) : Int) := by
      have : 1 ≤ L := Nat.pos_of_ne_zero hL0
      rw [show ((L - 1 : Nat) : Int) = (L : Int) - 1 by omega, ← hL]; word
    have hLlt : L - 1 < xs.length := by omega
    obtain ⟨lgL, HlgL⟩ : ∃ v, lns[L - 1]? = some v := ⟨_, List.getElem?_eq_getElem (by rw [Hlnl]; exact hLlt)⟩
    obtain ⟨xL, HxL⟩ : ∃ v, xs[L - 1]? = some v := ⟨_, List.getElem?_eq_getElem hLlt⟩
    have hxL : xs.getD (L - 1) default = xL := by rw [List.getD_eq_getElem?_getD, HxL]; rfl
    ihave #HlL := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => lineRO (GF := GF) a b) HlgL HxL $$ Hlr
    try wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (lw - W64 1) ∧ sint.Z (lw - W64 1) < sint.Z lsl.len by
      rw [hidxL, hxlen]; omega))]
    wp_apply wp_load_slice_index _ (sint.Z (lw - W64 1)) lns _ lgL (by rw [hidxL]; omega) $$ [] as -
    · iframe Hl; ipureintro; rw [hidxL, Int.toNat_natCast]; exact HlgL
    wp_join (Q := fun v => iprop(∃ (cs : GoSlice) (e : GoInterface), ⌜v = PairV #cs #e⌝ ∗ "Hlm" ∷ lm ↦$ mm ∗
        match tBC xs L with
        | .ok c => ⌜e = interface.nil⌝ ∗ setRO cs c
        | .error _ => ⌜e ≠ interface.nil⌝))
      at (Seq (App (Val exceptionDo) _) _) with [Hlm «$res0» «$res1» i]
    · try wp_auto
      wp_apply wp_map_lookup1 $$ [Hlm] as Hlm
      · iexact Hlm
      rw [show (zero_val w64) = W64 0 from rfl, hlwd]
      try wp_auto
      ihave #HlL0 := HlL
      iunfold lineRO at HlL0
      icases HlL0 with ⟨⟨%geL, #HgevL, #HgerL⟩, %HlfL, %laL, %lbL, %HlabL, #HcL0, #HcL1⟩
      iunfold eventRO at HgerL
      icases HgerL with ⟨%HefL, -, -, #HepropL⟩
      icases typedPointsto_split _ _ _ $$ HgevL with HgevLf
      simp only [TypedPointsto.typedPointstoDef]
      icases HgevLf with ⟨#GLName, -, -, -, -, -, -, #GLProp, -⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (lw - W64 1) ∧ sint.Z (lw - W64 1) < sint.Z lsl.len by
        rw [hidxL, hxlen]; omega))]
      wp_apply wp_load_slice_index _ (sint.Z (lw - W64 1)) lns _ lgL (by rw [hidxL]; omega) $$ [] as -
      · iframe Hl; ipureintro; rw [hidxL, Int.toNat_natCast]; exact HlgL
      try wp_auto
      simp only [tBC, hxL]
      rw [decide_strRel HefL.1 (show strRel go!"ApplyConfChange" "ApplyConfChange" by strRel_lit)]
      by_cases hac : xL.ev.name = "ApplyConfChange"
      · rw [decide_eq_true hac]
        wp_auto
        cases hp : xL.ev.prop with
        | none =>
          iunfold propsRO at HepropL
          icases HepropL with %Hpnull
          rw [Hpnull]
          wp_auto
          bc_fail [hac, hp]
        | some pr =>
        iunfold propsRO at HepropL
        icases HepropL with ⟨%gp, #Hgp, #Hccp⟩
        ihave %Hgpnn := typedPointsto_not_null _ _ _ $$ Hgp
        icases typedPointsto_split _ _ _ $$ Hgp with Hgpf
        simp only [TypedPointsto.typedPointstoDef]
        icases Hgpf with ⟨#PCC, -⟩
        rw [decide_eq_false Hgpnn]
        wp_auto
        cases hcc : pr.cc with
        | none =>
          icases Hccp with %Hccnull
          rw [Hccnull]
          wp_auto
          bc_fail [hac, hp, hcc]
        | some cc =>
        iunfold confChangeRO at Hccp
        icases Hccp with ⟨%gcc, #Hgcc, -, #Hnc⟩
        ihave %Hgccnn := typedPointsto_not_null _ _ _ $$ Hgcc
        icases typedPointsto_split _ _ _ $$ Hgcc with Hgccf
        simp only [TypedPointsto.typedPointstoDef]
        icases Hgccf with ⟨-, #CNewConf, -⟩
        rw [decide_eq_false Hgccnn]
        wp_auto
        cases hnc : cc.newconf with
        | none =>
          iunfold optSliceRO at Hnc
          icases Hnc with %Hncnull
          rw [Hncnull]
          wp_auto
          bc_fail [hac, hp, hcc, hnc]
        | some nc =>
        iunfold optSliceRO at Hnc
        icases Hnc with ⟨%ncsl, %ncvs, #Hncp, #Hncs, %Hncr⟩
        ihave %Hncnn := typedPointsto_not_null _ _ _ $$ Hncp
        rw [decide_eq_false Hncnn]
        wp_auto
        wp_apply wp_toSet ncsl _ ncvs nc $$ [] as %cset %okc ⟨-, Hcset⟩
        · iframe Hncs; ipureintro; exact Hncr
        try wp_auto
        cases htc : toSet nc with
        | none =>
          simp only [htc]
          icases Hcset with %Hokc
          subst Hokc
          wp_auto
          bc_fail [hac, hp, hcc, hnc, htc]
        | some c =>
        simp only [htc]
        icases Hcset with ⟨%Hokc, #Hcs⟩
        subst Hokc
        wp_auto
        iexists _, _
        iframe Hlm
        isplitl []
        · ipureintro; rfl
        simp [hac, hp, hcc, hnc, htc, Pure.pure, Except.pure]
        isplitl []
        · ipureintro; trivial
        iexact Hcs
      rw [decide_eq_false hac]
      wp_auto
      icases typedPointsto_split _ _ _ $$ ln with Hlnf
      simp only [TypedPointsto.typedPointstoDef]
      icases Hlnf with ⟨-, -, -, -, Lconf, -⟩
      icases array_acc _ 0 _ _ _ laL (Int.le_refl _) (by rw [HlabL]; rfl) $$ Lconf with ⟨Hc0p, -⟩
      rw [show sint.Z (W64 0) = 0 from rfl]
      wp_auto
      iexists _, _
      iframe Hlm
      isplitl []
      · ipureintro; rfl
      have : (xL.ev.name == "ApplyConfChange") = false := by simpa using hac
      simp only [this, Bool.false_eq_true, ite_false, Pure.pure, Except.pure]
      isplitl []
      · ipureintro; trivial
      iexact HcL0
    sorry
  sorry

end proof

end Etcdraft
end EtcdGrove
end Perennial

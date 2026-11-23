module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.NewReplay
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__Clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model__Step

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode map k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section pure
variable [GooseExts]

/-- **On a history the replay accepts, every operation steps** (the loop's rejecting branch is
unreachable), and the replay so far grows by its step. -/
theorem replay_step_ok {init : RM} {ops : List (Input × RResp)} {R : RReplay} {n : Nat}
    {acc : RM × GMap w64 RM × List RChange} {op : Input × RResp}
    (hR : replayL init ops = some R)
    (hacc : (ops.take n).foldl replayStepL (some (init, {[init.rv := init]}, [])) = some acc)
    (hop : ops[n]? = some op) :
    (rstepL op.1 acc.1 op.2).1 = true ∧
      (ops.take (n + 1)).foldl replayStepL (some (init, {[init.rv := init]}, [])) =
        replayStepL (some acc) op := by
  have htake : ops.take (n + 1) = ops.take n ++ [op] := by
    rw [List.take_add_one, hop]; rfl
  have hstep : (ops.take (n + 1)).foldl replayStepL (some (init, {[init.rv := init]}, [])) =
      replayStepL (some acc) op := by
    rw [htake, replayL_snoc, hacc]
  refine ⟨?_, hstep⟩
  cases hb : (rstepL op.1 acc.1 op.2).1
  · exfalso
    have hnone : replayStepL (some acc) op = none := by
      obtain ⟨a, b, c⟩ := acc
      simp only [replayStepL] at hb ⊢
      rw [hb]; rfl
    have : replayL init ops = none := by
      unfold replayL
      rw [← List.take_append_drop (n + 1) ops, List.foldl_append, hstep, hnone, replayStepL_none]
      rfl
    rw [this] at hR
    cases hR
  · rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]
variable [driver_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- A frozen model's struct, read-only. -/
theorem modelAt_struct (mp : Loc) (m : RM) :
    modelAt (GF := GF) mp m ⊢ ∃ il rl : Loc,
      isPkgInit pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 ∗ mp ↦□ (⟨il, m.rv, 0, m.pfx, versionerV, newFuncV, newListFuncV, rl⟩ :
        github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model) := by
  unfold modelAt modelRep modelVal
  iintro ⟨#Hi, %il, %rl, %M, #Hp, -, -, -⟩
  iexists il, rl
  iframe Hi Hp

theorem NewReplay.wp_proof
    (wp_Clone : Model.Clone.spec (GF := GF) (hG := hG))
    (wp_Step : Model.Step.spec (GF := GF) (hG := hG)) :
    NewReplay.spec (GF := GF) (hG := hG) := by
  intro mp init sl vs ops R hpre hR
  wp_start as ⟨#Hm, #Hsl, #Hops⟩
  wp_auto
  wp_apply wp_Clone mp init $$ [] as %mp0 Hm0
  · iframe #
  imod modelOwn_freeze mp0 init $$ Hm0 with #Hm0
  ihave ⟨%il0, %rl0, -, #Hp0⟩ := modelAt_struct mp0 init $$ Hm0
  iStructNamed Hp0
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc) go.uint64
    github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty.PointerType) as %sm Hsm
  (try wp_auto)
  wp_apply (wp_mapInsert go.uint64 sm ∅ init.rv mp0) $$ Hsm as Hsm
  (try wp_auto)
  ihave %Hsll := ownSlice_len $$ Hsl
  ihave %Hvl := BigSepL2.bigSepL2_length $$ Hops
  rename_i ig
  irename : (ig ↦ zero_val w64 : IProp GF) => gi
  ihave IH : iprop(∃ (n : w64) (opv : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
      (gv : w64) (stp : Loc) (st : RM) (ss : GMap w64 RM) (cs : List RChange) (M : GMap w64 Loc)
      (csl : GoSlice) (cvs : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change),
      "j" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ opv ∗ "gi" ∷ ig ↦ gv ∗
      "state" ∷ state_ptr ↦ stp ∗ "#Hst" ∷ modelAt stp st ∗
      "states" ∷ states_ptr ↦ sm ∗ "Hsm" ∷ sm ↦$ M ∗
      "#HM" ∷ □ (∀ (rv : w64) (q : Loc), ⌜M !! rv = some q⌝ → ∃ m, ⌜ss !! rv = some m⌝ ∗ modelAt q m) ∗
      "changes" ∷ changes_ptr ↦ csl ∗ "Hcsl" ∷ csl ↦* cvs ∗
      "Hcap" ∷ ownSliceCap github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change csl (DFrac.own 1) ∗
      "#Hcvs" ∷ ([∗list] cv;c ∈ cvs;cs, changeVRep cv c) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ops.length : Int) ∧
        (ops.take (sint.nat n)).foldl replayStepL (some (init, {[init.rv := init]}, [])) =
          some (st, ss, cs) ∧ ∀ rv, (M !! rv).isSome = (ss !! rv).isSome⌝) $$ [i op gi state Hsm states changes]
  · iexists W64 0, _, _, mp0, init, {[init.rv := init]}, [], <[init.rv := mp0]> ∅, slice.nil, []
    simp only [named]
    iframe
    iframe #
    ihave Hn0 := ownSlice_nil (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change)
      (GF := GF) (DFrac.own 1)
    ihave Hc0 := ownSliceCap_nil (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change)
      (GF := GF)
    iframe Hn0 Hc0
    isplitl []
    · imodintro
      iintro %rv %q %hq
      by_cases h : init.rv = rv
      · subst h
        rw [GMap.lookup_insert _ _ _] at hq
        cases hq
        iexists init
        iframe Hm0
        ipureintro; exact GMap.lookup_singleton _ _
      · rw [GMap.lookup_insert_ne _ _ h] at hq
        cases hq
    isplitl []
    · iapply BigSepL2.bigSepL2_nil.2; itrivial
    ipureintro
    refine ⟨by word, by word, rfl, fun rv => ?_⟩
    by_cases h : init.rv = rv
    · subst h; rw [GMap.lookup_insert _ _ _, GMap.lookup_singleton _ _]; rfl
    · rw [GMap.lookup_insert_ne _ _ h, GMap.lookup_singleton_ne _ h]; rfl
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ops.length := by word
    obtain ⟨op1, Hop1⟩ : ∃ o, ops[sint.nat n]? = some o := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨v, Hv⟩ : ∃ v, vs[sint.nat n]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hvl]; exact Hlt)⟩
    icases ownSlice_elem_acc (sint.Z n) v sl DFrac.discard vs Hn.1 Hv $$ Hsl with ⟨#Hle, -⟩
    ihave #Hopr := BigSepL2.bigSepL2_lookup (Φ := fun _ v op => opRep (GF := GF) v op) Hv Hop1 $$ Hops
    iunfold opRep at Hopr
    icases Hopr with ⟨#Hreq, #Hresp⟩
    obtain ⟨hsz, hfit, hother, hin, hparse, hlim, hflat, hlist, hobj⟩ := hpre (sint.nat n) _ op1 Hn.2.2.1 Hop1
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left Hbnd]
    wp_auto
    wp_apply wp_Step stp st op1.1 v.Request' v.Response' op1.2 hfit hin hparse hlim hother hflat hlist hobj hsz
      $$ [] as %b %np %cp ⟨%Hb, #Hnp, #Hcp⟩
    · iframe #
    obtain ⟨hok, hnext⟩ := replay_step_ok hR Hn.2.2.1 Hop1
    rw [hok] at Hb
    subst Hb
    (try wp_auto)
    ihave ⟨%ilN, %rlN, -, #HpN⟩ := modelAt_struct np _ $$ Hnp
    iStructNamed HpN
    wp_auto
    wp_apply (wp_mapInsert go.uint64 sm M (rstepL op1.1 st op1.2).2.1.rv np) $$ Hsm as Hsm
    (try wp_auto)
    have hfold : (ops.take (sint.nat (n + W64 1))).foldl replayStepL
        (some (init, {[init.rv := init]}, [])) = some ((rstepL op1.1 st op1.2).2.1,
          <[(rstepL op1.1 st op1.2).2.1.rv := (rstepL op1.1 st op1.2).2.1]> ss,
          cs ++ (rstepL op1.1 st op1.2).2.2.toList) := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, hnext]
      simp only [replayStepL, hok, ↓reduceIte]
    have hMs : ∀ rv, ((<[(rstepL op1.1 st op1.2).2.1.rv := np]> M) !! rv).isSome =
        ((<[(rstepL op1.1 st op1.2).2.1.rv := (rstepL op1.1 st op1.2).2.1]> ss) !! rv).isSome := by
      intro rv
      by_cases h : (rstepL op1.1 st op1.2).2.1.rv = rv
      · subst h; simp
      · rw [GMap.lookup_insert_ne _ _ h, GMap.lookup_insert_ne _ _ h]; exact Hn.2.2.2 rv
    ihave #HM' : □ (∀ (rv : w64) (q : Loc),
        ⌜(<[(rstepL op1.1 st op1.2).2.1.rv := np]> M) !! rv = some q⌝ → ∃ m,
          ⌜(<[(rstepL op1.1 st op1.2).2.1.rv := (rstepL op1.1 st op1.2).2.1]> ss) !! rv = some m⌝ ∗
            modelAt q m) $$ []
    · imodintro
      iintro %rv %q %hq
      by_cases h : (rstepL op1.1 st op1.2).2.1.rv = rv
      · subst h
        rw [GMap.lookup_insert _ _ _] at hq
        cases hq
        iexists _
        iframe Hnp
        ipureintro; exact GMap.lookup_insert _ _ _
      · rw [GMap.lookup_insert_ne _ _ h] at hq
        rw [GMap.lookup_insert_ne _ _ h]
        iapply HM $$ %rv %q %hq
    generalize hnc : (rstepL op1.1 st op1.2).2.2 = nc at hfold ⊢
    cases nc with
    | none =>
      iunfold changeRep at Hcp
      icases Hcp with %hcp
      subst hcp
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, _, _, np, _, _, _, _, csl, cvs
      iframe
      iframe #
      ipureintro
      refine ⟨by word, by word, ?_, hMs⟩
      simpa using hfold
    | some c =>
      iunfold changeRep at Hcp
      icases Hcp with ⟨%ox, %opx, #Hc, #Hox, #Hopx⟩
      ihave %Hcpn := typedPointsto_not_null $$ Hc
      rw [decide_eq_false Hcpn]
      wp_auto
      wp_apply wp_slice_literal (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change)
        [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change.mk c.key c.rv ox opx]
      isplitr
      · ipureintro; rfl
      iintro %lit ⟨Hlit, -⟩
      wp_apply wp_slice_append $$ [$Hcsl $Hcap $Hlit] as %csl' ⟨Hcsl', Hcap', -⟩
      (try wp_auto)
      wp_for_post
      iframe
      iexists n + W64 1, _, _, np, _, _, _, _, csl',
        cvs ++ [github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Change.mk c.key c.rv ox opx]
      iframe
      iframe #
      isplitl []
      · iapply BigSepL2.bigSepL2_snoc.2
        iframe #
        iunfold changeVRep
        iframe #
        ipureintro; exact ⟨rfl, rfl⟩
      ipureintro
      refine ⟨by word, by word, ?_, hMs⟩
      simpa using hfold
  · have hnl : sint.nat n = ops.length := by word
    rw [hnl, List.take_length] at Hn
    have hRe : R = ⟨ss, cs⟩ := by
      unfold replayL at hR
      rw [Hn.2.2.1] at hR
      cases hR; rfl
    subst hRe
    ihave ⟨%ilI, %rlI, #Hdrv, #HpI⟩ := modelAt_struct mp init $$ Hm
    iStructNamed HpI
    imod ownMap_persist _ _ _ $$ Hsm with #Hsm
    imod ownSlice_persist _ _ _ $$ Hcsl with #Hcsl
    iapply wp_fupd
    wp_auto
    ipersist «$r0»
    imodintro
    iapply HΦ
    isplitr
    · ipureintro; rfl
    unfold replayAt
    iframe Hdrv
    iexists sm, M, csl, cvs
    iframe «$r0» Hsm Hcsl Hcvs
    isplitr
    · ipureintro; exact Hn.2.2.2
    isplitr
    · ipureintro; exact replayL_rv hR
    isplitr
    · ipureintro; exact replayL_chgOk hR
    iapply BigSepM.bigSepM_forall_elim
    iintro %rv %q %hq
    iapply HM $$ %rv %q %hq


end proof

end k8s_correctness
end EtcdGrove
end Perennial

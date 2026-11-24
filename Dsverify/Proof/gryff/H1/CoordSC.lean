/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/CoordSC.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1b: the coordinator's `ShortCircuit` (the riskiest coordinator step: the sort, the reads
loop over the sorted `ShortReads`, the empty `ShortWrites` loop).
-/

module

public import Dsverify.Proof.gryff.H1.CoordSCDefs
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Lib.SortHyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal ReadOp WriteOp OngoingOp
  Msg Ev Ext Out Cmd Deps AMap StepRes)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [sortA : SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
theorem GryffCoordinator.ShortCircuit.wp_int (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3) (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
    (vt : model.ValTag) (n : w32) (vp : Loc) (gv : src.gryffproto.ValTag) (fo : Bool)
    (ropsR wopsR orR mtR fkR : Loc) (arS : GoSlice)
    (hsc : model.shortCircuit s n (vtOf gv) fo = some (s', outs)) (hrk : ropsKeyed s.rops) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        coordFix co ic k ropsR wopsR orR mtR fkR arS ∗
        amapRep ropsR s.rops (fun p r => readOpRep ρ p r) ∗ amapRep orR s.ongoingReqs ongoingOpRep ∗
        icoordOk ρ ic k C ∗ C vt (outs ++ o) ∗ vp ↦□ gv }}
      (App (App (App (coordM co go!"ShortCircuit") (Val #n)) (Val #vp)) (Val #fo))
    {{ RET #(); scPost ρ ropsR orR s' ∗ C vt o }} := by
  obtain ⟨op, hop, hloop, hfin⟩ := sc.shortCircuit_inv s s' n (vtOf gv) fo outs hsc
  simp only [coordM]
  wp_start as ⟨#Hfix, Hr, Ho, Hic, HC, #Hvp⟩
  unfold icoordOk
  simp only [specT]
  icases Hic with ⟨-, -, -, -, #HCR, -, -, #HPr, #HSt, -, -, -⟩
  icases (coordFix_open co ic k ropsR wopsR orR mtR fkR arS).1 $$ Hfix with ⟨#F1, #F2, #F3, #F4, #F5, #F6, #F7, #F8, #F9, #F10, #F11, #F12, #F13, #F14⟩
  icases (amapRep_open ropsR s.rops _).1 $$ Hr with ⟨%rm, Hrm, %Hrdom, Hrents⟩
  icases (amapRep_open orR s.ongoingReqs _).1 $$ Ho with ⟨%om, Hom, %Hodom, Hoents⟩
  obtain ⟨pn, hpn⟩ : ∃ pn, om !! n = some pn := by
    have := Hodom n; rw [hop] at this
    cases h : om !! n with
    | none => rw [h] at this; cases this
    | some p => exact ⟨p, rfl⟩
  icases amapEnts_take _ _ _ _ pn hpn $$ Hoents with ⟨Hoents, ⟨%op', %Hop', Hon⟩⟩
  rw [hop] at Hop'; cases Hop'
  icases ongoingOpRep_open pn op $$ Hon with ⟨%gn, %sw, Hpn, Hsr, Hsrc, Hsw, %Hgn⟩
  wp_auto
  wp_apply wp_map_lookup1 $$ Hom as Hom
  rw [hpn]
  simp only [Option.getD_some]
  wp_auto
  wp_apply wp_sort_Slice gn.ShortReads' op.shortReads _ iprop(keys_ptr ↦ gn.ShortReads') $$ [Hsr keys]
    as ⟨Hsr, keys⟩
  · iframe Hsr keys
    unfold lessOk
    iintro !> %ys %i %j %a %b %Hab ⟨Hsl, Hk⟩
    ihave %Hl := ownSlice_len $$ Hsl
    obtain ⟨ha, hb, hi0, hj0⟩ := Hab
    have hi : sint.Z i < sint.Z gn.ShortReads'.len := by
      have := (List.getElem?_eq_some_iff.1 ha).1
      simp only [sint.nat, sint.Z] at *; omega
    have hj : sint.Z j < sint.Z gn.ShortReads'.len := by
      have := (List.getElem?_eq_some_iff.1 hb).1
      simp only [sint.nat, sint.Z] at *; omega
    wp_auto
    rw [if_pos' ⟨hi0, hi⟩]
    wp_apply wp_load_slice_index gn.ShortReads' (sint.Z i) ys (DFrac.own 1) a hi0 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; exact ha
    rw [if_pos' ⟨hj0, hj⟩]
    wp_apply wp_load_slice_index gn.ShortReads' (sint.Z j) ys (DFrac.own 1) b hj0 $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; exact hb
    iframe Hsl Hk; ipureintro; rfl
  wp_apply wp_map_lookup1 $$ Hom as Hom
  rw [hpn]; simp only [Option.getD_some]
  wp_auto
  wp_apply wp_map_lookup1 $$ Hom as Hom
  rw [hpn]; simp only [Option.getD_some]
  wp_auto
  wp_apply wp_map_lookup1 $$ Hom as Hom
  rw [hpn]; simp only [Option.getD_some]
  wp_auto
  wp_printf HPr
  ihave Hoents := amapEnts_congr_del _ (sc.scInit s n op).ongoingReqs _ _ n (fun j hj => by
    simp only [sc.scInit]; rw [amap_put_get, if_neg hj]) $$ Hoents
  ihave HI : (∃ (iv : w64) (st : RState × List Out) (m : GMap w32 Loc) (rmv : GMap w64 Loc)
      (rem : List Out) (kv : w32),
      "i" ∷ i_ptr ↦ iv ∗ "k" ∷ k_ptr ↦ kv ∗ "Hom" ∷ orR ↦$ m ∗
      "Hoents" ∷ amapEnts st.1.ongoingReqs (GMap.delete n m) ongoingOpRep ∗
      "Hrm" ∷ ropsR ↦$ rmv ∗ "Hrents" ∷ amapEnts st.1.rops rmv (fun p r => readOpRep ρ p r) ∗
      "HC" ∷ C vt (rem ++ o) ∗ "Hpn" ∷ pn ↦ gn ∗ "Hsr" ∷ gn.ShortReads' ↦* sc.scKeys op ∗
      "%Hl" ∷ ⌜0 ≤ sint.Z iv ∧ scP s s' outs n (vtOf gv).v fo op pn (sint.nat iv) st m rmv rem⌝ :
      IProp GF) $$ [i k Hom Hoents Hrm Hrents HC Hpn Hsr]
  · iexists W64 0, (sc.scInit s n op, []), om, rm, outs, _
    dsimp only [sc.scInit, sc.scKeys]
    iframe i k Hom Hoents Hrm Hrents HC Hpn Hsr
    ipureintro
    refine ⟨by decide, by simp, hloop, by simp, fun j => ?_, Hrdom, Or.inr hpn,
      fun x hx => ?_, rfl, rfl, hrk⟩
    · simp only [sc.scInit]; rw [amap_put_get]
      by_cases hj : j = n
      · subst hj; simp [hpn]
      · simp only [hj, ↓reduceIte]; exact Hodom j
    · simp only [sc.scInit] at hx; rw [amap_put_get, if_pos rfl] at hx
      cases hx; rfl
  wp_for HI
  ihave %Hlen := ownSlice_len $$ Hsr
  obtain ⟨Hi0, Hb, Hlp, Hrem, Hod, Hrd, Hnn, Hnv, Hmx, Hwo⟩ := Hl
  wp_if_destruct
  · obtain ⟨kk, hkk⟩ : ∃ kk, (sc.scKeys op)[sint.nat iv]? = some kk := by
      refine ⟨_, List.getElem?_eq_getElem ?_⟩
      simp only [sint.nat, sint.Z] at *; omega
    have hdrop : (sc.scKeys op).drop (sint.nat iv) = kk :: (sc.scKeys op).drop (sint.nat iv + 1) := by
      obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 hkk
      rw [List.drop_eq_getElem_cons h1, h2]
    rw [if_pos' ⟨Hi0, Hif⟩]
    wp_apply wp_load_slice_index gn.ShortReads' (sint.Z iv) _ (DFrac.own 1) kk Hi0 $$ [Hsr] as Hsr
    · iframe Hsr; ipureintro; exact hkk
    have hbrk : (model.sge kk n && fo) = true ↔ (sint.Z n ≤ sint.Z kk ∧ fo = true) := by
      simp [model.sge, model.sle]
    rw [hdrop] at Hlp
    wp_if_destruct
    wp_if_destruct
    rotate_left
    · -- break
      have hd : sc.scF n (vtOf gv).v true kk st = .done st := by
        unfold sc.scF; rw [if_pos' (by simpa [model.sge, model.sle] using Hif)]
      simp only [sc.loopF, hd] at Hlp
      subst Hlp
      wp_for_post
      iapply HΦ
      have hr : rem = [] := by simpa using Hrem
      subst hr
      simp only [List.nil_append]
      iframe HC
      iapply (scClose ρ s' ropsR orR m rmv n pn gn sw
        { op with shortReads := sc.scKeys op } Hod Hrd Hnn Hnv Hgn)
      iframe Hrm Hrents Hom Hoents Hpn Hsr Hsrc Hsw
    simp only [sc.loopF, sc.scF_nb n (vtOf gv).v fo kk st (by simp [model.sge, model.sle, Hif])] at Hlp
    rotate_left
    simp only [sc.loopF, sc.scF_nb n (vtOf gv).v false kk st (by simp)] at Hlp
    all_goals (
      have hi1 : sint.nat (iv + W64 1) = sint.nat iv + 1 := by
        simp only [sint.nat, sint.Z] at *; word
      have hilt : sint.nat iv < (sc.scKeys op).length := by
        simp only [sint.nat, sint.Z] at *; omega
      wp_apply wp_map_lookup2 $$ Hom as Hom
      cases hmk : m !! kk with
      | none =>
        have hok : st.1.ongoingReqs.get? kk = none := by
          have := Hod kk; rw [hmk] at this
          cases h : st.1.ongoingReqs.get? kk with
          | none => rfl
          | some _ => rw [h] at this; cases this
        have hy : sc.scY (vtOf gv).v kk st = st := by simp only [sc.scY, hok]
        rw [hy] at Hlp
        simp only [Option.isSome_none, Option.getD_none]
        wp_auto
        wp_printf0 HPr
        wp_for_post
        iframe
        iexists iv + W64 1, st, m, rmv, rem, kk
        iframe
        ipureintro
        rw [hi1]
        exact ⟨by word, hilt, Hlp, Hrem, Hod, Hrd, Hnn, Hnv, Hmx, Hwo⟩
      | some p =>
        have hnv' : ∀ x, st.1.ongoingReqs.get? n = some x →
            x.requestId = gn.RequestId' ∧ x.clientId = gn.ClientId' := by
          intro x hx; rw [Hnv x hx]; exact ⟨Hgn.1.symm, Hgn.2.1.symm⟩
        icases orAcc st.1.ongoingReqs m n kk pn p gn hmk Hnn hnv' Hod $$ [Hoents Hpn] with
          ⟨%o', %g, %Hog, Hp, Hback⟩
        · iframe Hoents Hpn
        simp only [Option.isSome_some, Option.getD_some]
        wp_auto
        wp_apply wp_ShiftInts
        wp_apply wp_map_lookup2 $$ Hrm as Hrm
        obtain ⟨Ho', Hg1, Hg2⟩ := Hog
        rw [Hg1, Hg2]
        cases hrk : rmv !! model.shiftInts o'.requestId o'.clientId with
        | none =>
          have hrn : st.1.rops.get? (model.shiftInts o'.requestId o'.clientId) = none := by
            have := Hrd (model.shiftInts o'.requestId o'.clientId); rw [hrk] at this
            cases h : st.1.rops.get? (model.shiftInts o'.requestId o'.clientId) with
            | none => rfl
            | some _ => rw [h] at this; cases this
          have hy : sc.scY (vtOf gv).v kk st = st := by simp only [sc.scY, Ho', hrn]
          rw [hy] at Hlp
          icases Hback with ⟨Hback, -⟩
          ihave Hb2 := Hback $$ Hp
          icases Hb2 with ⟨Hoents, Hpn⟩
          simp only [Option.isSome_none, Option.getD_none]
          wp_auto
          wp_printf0 HPr
          wp_for_post
          iframe
          iexists iv + W64 1, st, m, rmv, rem, kk
          iframe
          ipureintro
          rw [hi1]
          exact ⟨by word, hilt, Hlp, Hrem, Hod, Hrd, Hnn, Hnv, Hmx, Hwo⟩
        | some rp =>
          icases amapEnts_take _ _ _ _ rp hrk $$ Hrents with ⟨Hrents, ⟨%read, %Hread, Hro⟩⟩
          icases (readOpRep_open ρ rp read).1 $$ Hro with
            ⟨%gr, %opr, %rws, %w, %gd, #Hwr, Hrp, #Hdep, Hop, Hmx, Hrv, Hrws, Hrwc, %Hgr⟩
          obtain ⟨Hrid, Hcid, Hkey, -⟩ := Hgr
          have hy : sc.scY (vtOf gv).v kk st =
              ({ st.1 with rops := st.1.rops.del (model.shiftInts o'.requestId o'.clientId),
                           ongoingReqs := st.1.ongoingReqs.del kk },
               st.2 ++ [.ext (.readReply o'.clientId o'.requestId (vtOf gv).v 1)]) := by
            simp only [sc.scY, Ho', Hread]
          rw [hy] at Hlp
          obtain ⟨rem', hrem'⟩ := sc.loopF_prefix _ _ _ _ _
          rw [Hlp] at hrem'
          have hrem : rem = .ext (.readReply o'.clientId o'.requestId (vtOf gv).v 1) :: rem' := by
            rw [← Hrem] at hrem'; simpa using hrem'
          simp only [Option.isSome_some, Option.getD_some]
          wp_auto
          wp_printf HPr
          wp_apply HSt as %_ ⟨%st0, %Hst0, Hstats⟩
          subst Hst0
          wp_apply StatsMap.Increment.wp' $$ [Hstats] as %_ -
          · stats_key
          · iframe Hstats
          rw [Hkey]
          wp_auto
          wp_apply HSt as %_ ⟨%st0, %Hst0, Hstats⟩
          subst Hst0
          wp_apply StatsMap.Increment.wp' $$ [Hstats] as %_ -
          · stats_key
          · iframe Hstats
          wp_apply wp_mapDelete $$ Hom as Hom
          wp_apply wp_mapDelete $$ Hrm as Hrm
          iStructNamedPrefix Hvp "gv"
          wp_auto
          rw [Hg1, Hg2, hrem, List.cons_append, show (vtOf gv).v = gv.V' from rfl]
          have hcid : read.clientId = o'.clientId := by -- H1b-R1
            have := congrArg (BitVec.setWidth 32) (Hwo.2 _ _ Hread)
            rw [shiftInts_low, shiftInts_low] at this
            exact this.symm
          wp_apply HCR $$ %o'.requestId %o'.clientId %gv.V' %vt %(rem' ++ o) %w [HC] as %_ ⟨%_, HC⟩
          · iframe HC; rw [← hcid]; iexact Hwr
          wp_for_post
          icases Hback with ⟨-, Hback⟩
          ihave Hb2 := Hback $$ Hp
          icases Hb2 with ⟨Hoents, Hpn⟩
          ihave Hrents := amapEnts_del _ _ _ _ $$ Hrents
          iclear Hrp Hop Hmx Hrv Hrws Hrwc
          iframe
          iexists iv + W64 1,
            ({ st.1 with rops := st.1.rops.del (model.shiftInts o'.requestId o'.clientId),
                         ongoingReqs := st.1.ongoingReqs.del kk },
             st.2 ++ [.ext (.readReply o'.clientId o'.requestId gv.V' 1)]), GMap.delete kk m,
            GMap.delete (model.shiftInts o'.requestId o'.clientId) rmv, rem', kk
          iframe
          ipureintro
          rw [hi1]
          exact ⟨by word, scP_del _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            ⟨Hrem, Hod, Hrd, Hnn, Hnv, Hmx, Hwo⟩ hilt Hlp hrem⟩)
  -- the loop ends: the model's loop is done too
  have hdrop : (sc.scKeys op).drop (sint.nat iv) = [] := by
    apply List.drop_eq_nil_of_le; simp only [sint.nat, sint.Z] at *; omega
  rw [hdrop] at Hlp
  simp only [sc.loopF] at Hlp
  subst Hlp
  have hr : rem = [] := by simpa using Hrem
  subst hr
  simp only [List.nil_append]
  wp_if_destruct
  rotate_left
  · iapply HΦ
    iframe HC
    iapply (scClose ρ s' ropsR orR m rmv n pn gn sw
      { op with shortReads := sc.scKeys op } Hod Hrd Hnn Hnv Hgn)
    iframe Hrm Hrents Hom Hoents Hpn Hsr Hsrc Hsw
  have hmn : m !! n = some pn := by
    obtain ⟨x, hx⟩ := hfin rfl
    rcases Hnn with h | h
    · have := Hod n; rw [h, hx] at this; cases this
    · exact h
  wp_apply wp_map_lookup1 $$ Hom as Hom
  rw [hmn]; simp only [Option.getD_some]
  wp_auto
  have hsw : sw = [] := Hgn.2.2.2.2
  subst hsw
  ihave %Hswl := ownSlice_len $$ Hsw
  ihave HI2 : ("i" ∷ i_ptr ↦ W64 0 : IProp GF) $$ [i]
  · iexact i
  wp_for HI2
  have hlen0 : decide (sint.Z (W64 0) < sint.Z gn.ShortWrites'.len) = false := by
    obtain ⟨h1, h2⟩ := Hswl
    have h3 : sint.Z (W64 0) = 0 := rfl
    rw [h3]; simp only [decide_eq_false_iff_not]
    simp only [List.length_nil, sint.nat, sint.Z] at h1 h2 ⊢; omega
  rw [hlen0]
  simp only [val_false_ne_true, decide_false, Bool.false_eq_true, ↓reduceIte, _root_.decide_true]
  wp_auto
  iapply HΦ
  iframe HC
  iapply (scClose ρ s' ropsR orR m rmv n pn gn []
    { op with shortReads := sc.scKeys op } Hod Hrd Hnn Hnv Hgn)
  iframe Hrm Hrents Hom Hoents Hpn Hsr Hsrc Hsw

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
theorem GryffCoordinator.ShortCircuit.wp_proof (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3) (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
    (vt : model.ValTag) (n : w32) (vp : Loc) (gv : src.gryffproto.ValTag) (fo : Bool)
    (hsc : model.shortCircuit s n (vtOf gv) fo = some (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C vt (outs ++ o) ∗ vp ↦□ gv }}
      (App (App (App (coordM co go!"ShortCircuit") (Val #n)) (Val #vp)) (Val #fo))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C vt o }} := by
  have hfr := sc.shortCircuit_frame s s' n (vtOf gv) fo outs hsc
  iintro %Φ ⟨#Hpkg, Hc, Hic, HC, #Hvp⟩ HΦ
  icases (coordOwn_open ρ co ic k s).1 $$ Hc with
    ⟨%ropsR, %wopsR, %orR, %mtR, %fkR, %arS, #Hfix, Hmisc, %Hrk, Hr, Hw, Ho⟩
  iapply (GryffCoordinator.ShortCircuit.wp_int ρ co ic k C s s' outs o vt n vp gv fo
    ropsR wopsR orR mtR fkR arS hsc Hrk) $$ [Hr Ho Hic HC]
  · iframe Hpkg Hfix Hr Ho Hic HC Hvp
  iintro !> ⟨Hpost, HC⟩
  iapply HΦ
  iframe HC
  unfold scPost
  icases Hpost with ⟨Hr, Ho⟩
  iapply (coordOwn_open ρ co ic k s').2
  iexists ropsR, wopsR, orR, mtR, fkR, arS
  have hrk' := shortCircuit_ropsKeyed s s' n (vtOf gv) fo outs hsc Hrk
  rw [hfr] at hrk' ⊢
  dsimp only at hrk' ⊢
  iframe Hfix Hmisc Hr Hw Ho %hrk'

end

end Perennial.gryff.replica2

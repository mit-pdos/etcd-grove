/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/CoordW1.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1b: the coordinator's `HandleWrite1Reply`.
-/
module

public import Dsverify.Proof.gryff.H1.CoordW2Defs
public import Dsverify.Proof.gryff.H1.CoordSpecs
public import Dsverify.Proof.gryff.H1.PureWrite1
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Replica2.Specs

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
variable [strconvA : strconv.Assumptions] -- N-5


/-- A write op's struct after the Write1 reply's update: the fields other than the max value-tag
and the Write1 counters are `g`'s. -/
def w1Agree (g g' : src.gryffcommon.WriteOp) : Prop :=
  g'.Op' = g.Op' ∧ g'.N' = g.N' ∧ g'.WriteValue' = g.WriteValue' ∧
    g'.MaxAppliedTag' = g.MaxAppliedTag' ∧ g'.ForceWrite' = g.ForceWrite' ∧
    g'.numWrite2Applies' = g.numWrite2Applies' ∧ g'.numWrite2Replies' = g.numWrite2Replies' ∧
    g'.sentWrite2Round' = g.sentWrite2Round' ∧ g'.WriteTag' = g.WriteTag' ∧
    g'.startedShortcircuitTimeout' = g.startedShortcircuitTimeout'

/-- `w1Upd` keeps the op's identity, value, dependency, Write2 state and tag. -/
theorem w1Upd_fields (w : WriteOp) (vt : model.ValTag) :
    (w1Upd w vt).requestId = w.requestId ∧ (w1Upd w vt).clientId = w.clientId ∧
    (w1Upd w vt).n = w.n ∧ (w1Upd w vt).writeValue = w.writeValue ∧ (w1Upd w vt).dep = w.dep ∧
    (w1Upd w vt).numWrite2Applies = w.numWrite2Applies ∧
    (w1Upd w vt).numWrite2Replies = w.numWrite2Replies ∧
    (w1Upd w vt).sentWrite2Round = w.sentWrite2Round ∧ (w1Upd w vt).writeTag = w.writeTag := by
  unfold w1Upd; split
  · simp
  · split <;> simp

/-- A write op's rep from its opened parts (the max value-tag cell `gm`). -/
theorem w1_wo (ρ : Repl2Names) (co p : Loc) (g : src.gryffcommon.WriteOp) (op : src.gryffcommon.Op)
    (wr : Loc) (gd : src.gryffproto.Dep) (gm : src.gryffproto.ValTag) (W : WriteOp)
    (hm : vtOf gm = W.maxValTag)
    (hg : op.RequestId' = W.requestId ∧ op.ClientId' = W.clientId ∧ op.Key' = W64 0 ∧ g.N' = W.n ∧
      depOf gd = W.dep ∧ g.WriteValue' = W.writeValue ∧ g.ForceWrite' = W32 1 ∧
      g.numWrite1Applies' = W.numWrite1Applies ∧ g.numWrite1Replies' = W.numWrite1Replies ∧
      g.numWrite2Applies' = W.numWrite2Applies ∧ g.numWrite2Replies' = W.numWrite2Replies ∧
      g.sentWrite2Round' = W.sentWrite2Round ∧ g.startedShortcircuitTimeout' = false) :
    writerIs (GF := GF) ρ W.clientId wr ∗ p ↦ g ∗ g.Op' ↦ op ∗ op.Dep' ↦□ gd ∗
      (⌜g.MaxAppliedTag' = co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"]⌝ ∨
        ∃ gt : src.gryffproto.Tag, g.MaxAppliedTag' ↦□ gt) ∗
      g.maxValTag' ↦□ gm ∗
      (match W.writeTag with
       | none => iprop(⌜g.WriteTag' = Loc.null⌝)
       | some t => iprop(∃ gt : src.gryffproto.Tag, g.WriteTag' ↦□ gt ∗ ⌜tagOf gt = t⌝)) ⊢
    writeOpRep ρ co p W := by
  iintro ⟨#Hwr, Hp, Hop, #Hgd, Hmat, #Hgm, Hwt⟩
  iapply (writeOpRep_open ρ co p _).2
  iexists g, op, wr, gd
  iframe Hwr Hp Hop Hgd Hmat Hwt
  isplitl []
  · unfold optVtRep; iexists gm; iframe Hgm; ipureintro; exact hm
  ipureintro; exact hg

variable [scD : GryffSCDeps (GF := GF)]

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
theorem GryffCoordinator.HandleWrite1Reply.wp_proof (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3) (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
    (m : model.Write1ReplyM) (rep : w32) (vp : Loc) (gv : src.gryffproto.ValTag)
    (hv : vtOf gv = m.vt) (hid : s.id = rid32 k) -- H1-R9
    (hstep : model.stepR k s (.msg (.write1Reply m)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) ∗ vp ↦□ gv }}
      (App (App (App (App (coordM co go!"HandleWrite1Reply")
        (Val #(model.shiftInts m.requestId m.clientId))) (Val #m.clientId)) (Val #rep)) (Val #vp))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }} := by
  have hcase := stepWrite1Reply_inv k s s' m outs hstep
  simp only [coordM]
  wp_start as ⟨Hc, #Hic, HC, #Hvp⟩
  ihave Hparts := (show icoordOk ρ ic k C ⊢ _ from by unfold icoordOk; exact .rfl) $$ Hic
  simp only [specT]
  icases Hparts with ⟨-, -, -, #HS2, -, #HCW, -, #HPr, #HSt, -, -, -⟩
  icases (coordOwn_open ρ co ic k s).1 $$ Hc with
    ⟨%ropsR, %wopsR, %orR, %mtR, %fkR, %arS, #Hfix, Hmisc, %Hrk, Hr, Hw, Ho⟩
  icases (coordFix_open co ic k ropsR wopsR orR mtR fkR arS).1 $$ Hfix with ⟨#F1, #F2, #F3, #F4, #F5, #F6, #F7, #F8, #F9, #F10, #F11, #F12, #F13, #F14⟩
  icases (amapRep_open wopsR s.wops _).1 $$ Hw with ⟨%wm, Hwm, %Hwdom, Hwents⟩
  wp_auto
  wp_printf HPr
  wp_apply wp_map_lookup2 $$ Hwm as Hwm
  cases hg : wm !! model.shiftInts m.requestId m.clientId with
  | none =>
    have hgm : s.wops.get? (model.shiftInts m.requestId m.clientId) = none := by
      have := Hwdom (model.shiftInts m.requestId m.clientId); rw [hg] at this
      cases h : s.wops.get? (model.shiftInts m.requestId m.clientId) with
      | none => rfl
      | some _ => rw [h] at this; cases this
    rcases hcase with ⟨-, rfl, rfl⟩ | ⟨w, hw, -⟩
    rotate_left
    · rw [hgm] at hw; cases hw
    simp only [Option.isSome_none]
    wp_auto
    wp_printf0 HPr
    iapply HΦ
    simp only [List.nil_append]
    iframe HC
    iapply (coordOwn_open ρ co ic k _).2
    iexists ropsR, wopsR, orR, mtR, fkR, arS
    iframe Hfix Hmisc Hr Ho %Hrk
    iapply (amapRep_open wopsR _ _).2
    iexists wm
    iframe Hwm Hwents
    ipureintro; exact Hwdom
  | some p =>
    icases amapEnts_take _ _ _ _ p hg $$ Hwents with ⟨Hwents, ⟨%w, %Hw, Hwo⟩⟩
    icases (writeOpRep_open ρ co p w).1 $$ Hwo with
      ⟨%g, %op, %wr, %gd, #Hwr, Hp, Hop, #Hgd, Hmat, Hmvt, Hwt, %Hgw⟩
    obtain ⟨Hg1, Hg2, Hg3, Hg4, Hg5, Hg6, Hg7, Hg8, Hg9, Hg10, Hg11, Hg12, Hg13⟩ := Hgw
    rcases hcase with ⟨hn, -⟩ | ⟨w', hw', hcase⟩
    · rw [hn] at Hw; cases Hw
    rw [Hw] at hw'; cases hw'
    simp only [Option.isSome_some, Option.getD_some]
    wp_auto
    wp_join iprop(c_ptr ↦ co ∗ replicaId_ptr ↦ rep ∗ write_ptr ↦ p ∗ p ↦ g) at next
      with [c replicaId write Hp] as ⟨c, replicaId, write, Hp⟩
    · cases g.sentWrite2Round'
      · wp_auto
        wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
        subst Hst'
        wp_apply StatsMap.IncrementStrInt.wp' $$ [Hstats] as %_ -
        · stats_key
        · iframe Hstats
        wp_join_done
      · wp_auto
        wp_join_done
    unfold optVtRep
    icases Hmvt with ⟨%gm, #Hgm, %Hgmv⟩
    ihave #Hvp2 := Hvp
    ihave #Hgm2 := Hgm
    iStructNamedPrefix Hvp "gv"
    iStructNamedPrefix Hgm "gm"
    wp_auto
    have hvt : tagOf gv.T' = m.vt.t := by rw [← hv]; rfl
    have hvv : gv.V' = m.vt.v := by rw [← hv]; rfl
    have hmt : tagOf gm.T' = w.maxValTag.t := by rw [← Hgmv]; rfl
    have hmv : gm.V' = w.maxValTag.v := by rw [← Hgmv]; rfl
    wp_apply Tag.wp_GreaterThan $$ [$gvT] as -
    rw [hvt, hmt]
    wp_join iprop(∃ (g' : src.gryffcommon.WriteOp) (gm' : src.gryffproto.ValTag),
        write_ptr ↦ p ∗ vt_ptr ↦ vp ∗ p ↦ g' ∗ g'.maxValTag' ↦□ gm' ∗
        ⌜vtOf gm' = (w1Upd w m.vt).maxValTag ∧
          g'.numWrite1Applies' = (w1Upd w m.vt).numWrite1Applies ∧
          g'.numWrite1Replies' = (w1Upd w m.vt).numWrite1Replies ∧ w1Agree g g'⌝) at next
      with [write vt Hp] as ⟨%g', %gm', write, vt, Hp, #Hgm', %Hg'⟩
    · cases hgt : m.vt.t.gt w.maxValTag.t
      · wp_auto
        wp_apply Tag.wp_Equals $$ [$gvT] as -
        rw [hvt, hmt]
        cases heq : m.vt.t.eqT w.maxValTag.t
        · wp_auto
          wp_join_done
          iexists _, gm
          iframe write vt Hp Hgm2
          ipureintro
          simp only [w1Upd, hgt, heq, Bool.false_eq_true, ↓reduceIte, Bool.false_and]
          exact ⟨Hgmv, Hg8, by rw [Hg9]; rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
        · wp_auto
          wp_if_destruct
          · wp_if_destruct
            · wp_join_done
              iexists _, gm
              iframe write vt Hp Hgm2
              ipureintro
              have h3 : (m.vt.v == w.maxValTag.v && model.sge w.maxValTag.v 0) = true := by
                simp only [Bool.and_eq_true, beq_iff_eq, model.sge, model.sle, decide_eq_true_eq]
                rw [← hvv, ← hmv]
                exact ⟨‹gv.V' = gm.V'›, by simpa using ‹sint.Z (W64 0) ≤ sint.Z gm.V'›⟩
              simp only [w1Upd, hgt, heq, h3, Bool.false_eq_true, ↓reduceIte, Bool.and_self]
              exact ⟨Hgmv, by rw [Hg8]; rfl, by rw [Hg9]; rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
            · wp_join_done
              iexists _, gm
              iframe write vt Hp Hgm2
              ipureintro
              have h3 : (m.vt.v == w.maxValTag.v && model.sge w.maxValTag.v 0) = false := by
                simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne, model.sge, model.sle,
                  decide_eq_false_iff_not]
                right; rw [← hmv]; simpa using ‹¬sint.Z (W64 0) ≤ sint.Z gm.V'›
              simp only [w1Upd, hgt, heq, h3, Bool.false_eq_true, ↓reduceIte, Bool.and_false]
              exact ⟨Hgmv, Hg8, by rw [Hg9]; rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
          · wp_join_done
            iexists _, gm
            iframe write vt Hp Hgm2
            ipureintro
            have h3 : (m.vt.v == w.maxValTag.v && model.sge w.maxValTag.v 0) = false := by
              simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
              left; rw [← hvv, ← hmv]; exact ‹¬gv.V' = gm.V'›
            simp only [w1Upd, hgt, heq, h3, Bool.false_eq_true, ↓reduceIte, Bool.true_and]
            exact ⟨Hgmv, Hg8, by rw [Hg9]; rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
      · wp_auto
        wp_if_destruct
        · wp_join_done
          iexists _, gv
          iframe write vt Hp Hvp2
          ipureintro
          have h0 : model.sge m.vt.v 0 = true := by
            simp only [model.sge, model.sle, decide_eq_true_eq]; rw [← hvv]; simpa using Hif
          simp only [w1Upd, hgt, h0, ↓reduceIte]
          exact ⟨hv, rfl, by rw [Hg9]; rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
        · wp_join_done
          iexists _, gv
          iframe write vt Hp Hvp2
          ipureintro
          have h0 : model.sge m.vt.v 0 = false := by
            simp only [model.sge, model.sle, decide_eq_false_iff_not]; rw [← hvv]; simpa using Hif
          simp only [w1Upd, hgt, h0, ↓reduceIte, Bool.false_eq_true]
          exact ⟨hv, rfl, by rw [Hg9]; rfl, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    obtain ⟨Hgmv', HgA, HgR, Ha1, Ha2, Ha3, Ha4, Ha5, Ha6, Ha7, Ha8, Ha9, Ha10⟩ := Hg'
    repeat (first | wp_auto | rw [Ha1])
    wp_printf HPr
    repeat (first | wp_auto | rw [Ha1])
    wp_printf HPr
    repeat (first | wp_auto | rw [Ha1])
    wp_printf HPr
    obtain ⟨hW1, hW2, hW3, hW4, hW5, hW6, hW7, hW8, hW9⟩ := w1Upd_fields w m.vt
    have hinv := w1Tail_inv _ _ _ _ _ hcase
    have h2 : BitVec.sdiv (W64 3) (W64 2) + W64 1 = model.NHALF + 1 := by decide
    rw [h2, HgR]
    have hwo : ∀ W' : WriteOp, W' = w1Upd w m.vt → (writerIs (GF := GF) ρ W'.clientId wr ∗ p ↦ g' ∗ g.Op' ↦ op ∗
        op.Dep' ↦□ gd ∗
        (⌜g.MaxAppliedTag' = co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"]⌝ ∨
          ∃ gt : src.gryffproto.Tag, g.MaxAppliedTag' ↦□ gt) ∗ g'.maxValTag' ↦□ gm' ∗
        (match w.writeTag with
         | none => iprop(⌜g.WriteTag' = Loc.null⌝)
         | some t => iprop(∃ gt : src.gryffproto.Tag, g.WriteTag' ↦□ gt ∗ ⌜tagOf gt = t⌝)) ⊢
        writeOpRep ρ co p W') := by
      intro W' hW'
      subst hW'
      rw [← Ha1, ← Ha4, ← Ha9, ← hW9]
      exact w1_wo ρ co p g' op wr gd gm' _ Hgmv'
        ⟨by rw [hW1]; exact Hg1, by rw [hW2]; exact Hg2, Hg3, by rw [Ha2, hW3]; exact Hg4,
          by rw [hW5]; exact Hg5, by rw [Ha3, hW4]; exact Hg6, by rw [Ha5]; exact Hg7, HgA, HgR,
          by rw [Ha6, hW6]; exact Hg10, by rw [Ha7, hW7]; exact Hg11, by rw [Ha8, hW8]; exact Hg12,
          by rw [Ha10]; exact Hg13⟩
    wp_if_destruct
    · rw [HgA, h2]
      rcases hinv with ⟨-, hA, s2, outs2, hsc, rfl, rfl⟩ | ⟨-, hA, hsent, hm, rfl⟩ | ⟨hq, rfl, rfl⟩
      · -- fast path: a quorum of Write1 applies
        rw [show decide _ = true from hA]
        wp_auto
        wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
        subst Hst'
        wp_apply StatsMap.Increment.wp' $$ [Hstats] as %_ -
        · stats_key
        · iframe Hstats
        rw [Ha1]
        wp_auto
        rw [Hg3]
        wp_auto
        wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
        subst Hst'
        wp_apply StatsMap.Increment.wp' $$ [Hstats] as %_ -
        · stats_key
        · iframe Hstats
        wp_printf HPr
        rw [Ha2, Hg4, ← hW3]
        rw [← Hgmv'] at hsc
        have hfr := sc.shortCircuit_frame _ _ _ _ _ _ hsc
        have hrk' := shortCircuit_ropsKeyed _ _ _ _ _ _ hsc Hrk -- H1b-R1
        wp_apply (GryffSCDeps.shortCircuit (GF := GF) (hG := hG) ρ co ic k C s _ outs2
          ([.ext (.writeReply (w1Upd w m.vt).clientId (w1Upd w m.vt).requestId 1)] ++ o) s.storeVT
          _ g'.maxValTag' gm' true ropsR wopsR orR mtR fkR arS hsc Hrk) $$ [Hr Ho HC] as ⟨Hpost, HC⟩
        · iframe Hfix Hr Ho Hic Hgm'
          rw [List.append_assoc] at *
          iframe HC
        wp_apply wp_mapDelete $$ Hwm as Hwm
        rw [Ha2, Hg4, ← hW3]
        unfold scPost
        icases Hpost with ⟨Hr, Ho⟩
        icases (amapRep_open orR _ _).1 $$ Ho with ⟨%om, Hom, %Hodom, Hoents⟩
        wp_apply wp_mapDelete $$ Hom as Hom
        repeat (first | wp_auto | rw [Ha1])
        rw [Hg1, Hg2, ← hW1, ← hW2, List.singleton_append]
        wp_apply HCW $$ %(w1Upd w m.vt).requestId %(w1Upd w m.vt).clientId %s.storeVT %o %wr [HC]
          as %_ ⟨%_, HC⟩
        · iframe HC; rw [hW2]; iexact Hwr
        iapply HΦ
        rw [hfr]
        simp only [model.RState.storeVT]
        iframe HC
        iapply (coordOwn_open ρ co ic k _).2
        iexists ropsR, wopsR, orR, mtR, fkR, arS
        dsimp only
        iframe Hfix Hr %hrk'
        isplitl [Hmisc]
        · iapply (coordMisc_mono co s.maxN (s.wops = [])
            (s.wops.del (model.shiftInts m.requestId m.clientId) = [])
            ((s.wops.map (fun e => e.1.toNat)).Pairwise (· < ·))
            (((s.wops.del (model.shiftInts m.requestId m.clientId)).map (fun e => e.1.toNat)).Pairwise (· < ·))
            mtR fkR (fun h => by rw [h]; rfl)
            (fun h => List.Pairwise.sublist (List.filter_sublist.map _) h)) $$ Hmisc
        isplitl [Hwm Hwents]
        · iapply (amapRep_open wopsR _ _).2
          iexists _
          iframe Hwm
          isplitl []
          · ipureintro; intro key
            by_cases hk : key = model.shiftInts m.requestId m.clientId
            · subst hk; rw [GMap.lookup_delete, amap_del_get_self]; rfl
            · rw [GMap.lookup_delete_ne _ (Ne.symm hk), amap_del_get_ne _ _ _ hk]; exact Hwdom key
          iapply amapEnts_del $$ Hwents
        iapply (amapRep_open orR _ _).2
        iexists _
        iframe Hom
        isplitl []
        · ipureintro; intro key
          by_cases hk : key = (w1Upd w m.vt).n
          · subst hk; rw [GMap.lookup_delete, amap_del_get_self]; rfl
          · rw [GMap.lookup_delete_ne _ (Ne.symm hk), amap_del_get_ne _ _ _ hk]; exact Hodom key
        iapply amapEnts_drop $$ Hoents
      · -- slow path: Write2s
        rw [show decide _ = false from hA]
        wp_auto
        have hs' : g'.sentWrite2Round' = false := by rw [Ha8, Hg12, ← hW8]; exact hsent
        rw [hs']
        wp_auto
        rw [Ha10, Hg13]
        wp_auto
        ihave #Hgm'2 := Hgm'
        iStructNamedPrefix Hgm'2 "gmx"
        iStructNamedPrefix gmxT "gmt"
        wp_auto
        wp_join iprop(c_ptr ↦ co) with [c] as c
        · wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
          subst Hst'
          wp_apply StatsMap.Increment.wp' $$ [Hstats] as %_ -
          · stats_key
          · iframe Hstats
          wp_join_done
        dsimp only
        repeat (first | wp_auto | rw [Ha1])
        icases (amapRep_open orR s.ongoingReqs _).1 $$ Ho with ⟨%om, Hom, %Hodom, Hoents⟩
        wp_apply wp_map_lookup1 $$ Hom as Hom
        wp_printf HPr
        ihave Ho : (amapRep orR s.ongoingReqs ongoingOpRep : IProp GF) $$ [Hom Hoents]
        · iapply (amapRep_open orR _ _).2
          iexists om
          iframe Hom Hoents
          ipureintro; exact Hodom
        wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
        subst Hst'
        wp_apply StatsMap.IncrementStrInt.wp' $$ [Hstats] as %_ -
        · stats_key
        · iframe Hstats
        ipersist «$r0»
        have htag : tagOf { Ts' := gm'.T'.Ts' + W32 1, Cid' := m.clientId, Rmwc' := W32 0 } =
            w1Tag (w1Upd w m.vt) m.clientId := by
          simp only [w1Tag, ← Hgmv', tagOf, vtOf]; rfl
        have hsend : sendsTo [W32 0, W32 1, W32 2] (.write2 (write2Msg k
            { w1Upd w m.vt with writeTag := some (w1Tag (w1Upd w m.vt) m.clientId) }
            (w1Tag (w1Upd w m.vt) m.clientId))) = some outs := by
          rw [hid] at hm; exact hm
        have hpre : ({ w1Upd w m.vt with writeTag := some (w1Tag (w1Upd w m.vt) m.clientId) } :
            WriteOp).writeTag = some (w1Tag (w1Upd w m.vt) m.clientId) ∧
            sendsTo [W32 0, W32 1, W32 2] (.write2 (write2Msg k
            { w1Upd w m.vt with writeTag := some (w1Tag (w1Upd w m.vt) m.clientId) }
            (w1Tag (w1Upd w m.vt) m.clientId))) = some outs := ⟨rfl, hsend⟩
        ihave HS := HS2 $$ %co %p %_ %_ %arS %_ %s.storeVT %outs %o %hpre
        ihave Hwo := w1_wo ρ co p { g' with Op' := g.Op', WriteTag' := «$r0_ptr» } op wr gd gm'
          { w1Upd w m.vt with writeTag := some (w1Tag (w1Upd w m.vt) m.clientId) } Hgmv'
          ⟨by rw [hW1]; exact Hg1, by rw [hW2]; exact Hg2, Hg3, by show g'.N' = _; rw [Ha2, hW3]; exact Hg4,
            by rw [hW5]; exact Hg5, by show g'.WriteValue' = _; rw [Ha3, hW4]; exact Hg6,
            by show g'.ForceWrite' = _; rw [Ha5]; exact Hg7, HgA, HgR,
            by show g'.numWrite2Applies' = _; rw [Ha6, hW6]; exact Hg10,
            by show g'.numWrite2Replies' = _; rw [Ha7, hW7]; exact Hg11,
            by show g'.sentWrite2Round' = _; rw [Ha8, hW8]; exact Hg12,
            by show g'.startedShortcircuitTimeout' = _; rw [Ha10]; exact Hg13⟩ $$ [Hp Hop Hmat]
        · rw [hW2]
          iframe Hwr Hp Hgd Hgm' Hop
          dsimp only
          rw [Ha4]
          iframe Hmat
          iexists _
          iframe «$r0»
          ipureintro; exact htag
        wp_apply HS $$ [HC Hwo] as %_ ⟨%_, HC, Hwo⟩
        · iframe HC Hwo F9
        icases (writeOpRep_open ρ co p _).1 $$ Hwo with
          ⟨%g4, %op4, %wr4, %gd4, #Hwr4, Hp4, Hop4, #Hgd4, Hmat4, Hmvt4, Hwt4, %Hg4⟩
        wp_auto
        iapply HΦ
        simp only [model.RState.storeVT]
        iframe HC
        ihave Hwo : (writeOpRep ρ co p (w1Slow (w1Upd w m.vt) m.clientId) : IProp GF)
          $$ [Hp4 Hop4 Hmat4 Hmvt4 Hwt4]
        · iapply (writeOpRep_open ρ co p _).2
          iexists _, op4, wr4, gd4
          simp only [w1Slow]
          iframe Hwr4 Hp4 Hop4 Hgd4 Hmat4 Hmvt4 Hwt4
          ipureintro
          obtain ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12, H13⟩ := Hg4
          exact ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, rfl, H13⟩
        iapply coordOwn_close_wput ρ co ic k s ropsR wopsR orR mtR fkR arS wm _ p _ hg Hwdom Hrk
        iframe Hfix Hr Ho Hwm Hwents Hwo
        iapply coordMisc_mono _ _ _ _ _ _ _ _
          (fun h => absurd h (wops_ne_nil _ _ _ Hw)) (wops_sorted_put _ _ _) $$ Hmisc
      · rcases hq with hq | ⟨hA, hs⟩
        · exfalso; simp only [model.sge, model.sle, _root_.decide_eq_false_iff_not] at hq; exact hq Hif
        rw [show decide _ = false from hA]
        wp_auto
        have hs' : g'.sentWrite2Round' = true := by rw [Ha8, Hg12, ← hW8]; exact hs
        rw [hs']
        wp_auto
        iapply HΦ
        simp only [model.RState.storeVT, List.nil_append]
        iframe HC
        ihave Hwo := hwo _ rfl $$ [Hp Hop Hmat Hwt]
        · rw [hW2]; iframe Hwr Hp Hop Hgd Hmat Hgm' Hwt
        iapply coordOwn_close_wput ρ co ic k s ropsR wopsR orR mtR fkR arS wm _ p _ hg Hwdom Hrk
        iframe Hfix Hr Ho Hwm Hwents Hwo
        iapply coordMisc_mono _ _ _ _ _ _ _ _
          (fun h => absurd h (wops_ne_nil _ _ _ Hw)) (wops_sorted_put _ _ _) $$ Hmisc
    · -- no quorum yet: the op is updated in place
      rcases hinv with ⟨hq, -⟩ | ⟨hq, -⟩ | ⟨-, rfl, rfl⟩
      · exfalso; simp only [model.sge, model.sle, _root_.decide_eq_true_eq] at hq; exact Hif hq
      · exfalso; simp only [model.sge, model.sle, _root_.decide_eq_true_eq] at hq; exact Hif hq
      iapply HΦ
      simp only [model.RState.storeVT, List.nil_append]
      iframe HC
      ihave Hwo := hwo _ rfl $$ [Hp Hop Hmat Hwt]
      · rw [hW2]; iframe Hwr Hp Hop Hgd Hmat Hgm' Hwt
      iapply coordOwn_close_wput ρ co ic k s ropsR wopsR orR mtR fkR arS wm _ p _ hg Hwdom Hrk
      iframe Hfix Hr Ho Hwm Hwents Hwo
      iapply coordMisc_mono _ _ _ _ _ _ _ _
        (fun h => absurd h (wops_ne_nil _ _ _ Hw)) (wops_sorted_put _ _ _) $$ Hmisc

end

end Perennial.gryff.replica2

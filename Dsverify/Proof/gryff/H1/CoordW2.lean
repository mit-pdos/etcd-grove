/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/CoordW2.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1b: the coordinator's `HandleWrite2Reply` (`ShortCircuit` on the write's own state).
-/
module

public import Dsverify.Proof.gryff.H1.CoordSC
public import Dsverify.Proof.gryff.H1.PureWrite
public import Dsverify.Proof.gryff.PureL.Frame
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

theorem amap_put_ne_nil {n : Nat} {V : Type} (l : AMap n V) (k : BitVec n) (v : V) :
    l.put k v ≠ [] := by
  cases l with
  | nil => simp [model.AMap.put]
  | cons e t =>
    simp only [model.AMap.put]
    split
    · simp
    · split <;> simp

theorem amap_put_del {n : Nat} {V : Type} (l : AMap n V) (k : BitVec n) (v : V) :
    (l.put k v).del k = l.del k := by
  induction l with
  | nil => simp [model.AMap.put, model.AMap.del]
  | cons e t ih =>
    obtain ⟨k', v'⟩ := e
    simp only [model.AMap.put]
    by_cases h1 : k = k'
    · subst h1; simp [model.AMap.del]
    · simp only [h1, ↓reduceIte]
      have hne : (k' != k) = true := bne_iff_ne.2 (Ne.symm h1)
      split
      · simp [model.AMap.del, hne]
      · simp only [model.AMap.del, List.filter_cons, hne, ↓reduceIte] at ih ⊢
        rw [ih]

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [sortA : SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5


instance pure_wand_persistent_h1b (φ : Prop) (P : IProp GF) [Persistent P] :
    Persistent iprop(⌜φ⌝ -∗ P) where
  persistent := by
    by_cases h : φ
    · iintro H
      ihave #HP := H $$ %h
      imodintro
      iintro -
      iexact HP
    · iintro -
      imodintro
      iintro %hφ
      exact absurd hφ h

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance (priority := high) icoordOk_persistent' (ρ : Repl2Names) (ic : GoInterface) (k : Fin 3)
    (C : model.ValTag → List Out → IProp GF) : Persistent (icoordOk ρ ic k C) := by
  unfold icoordOk specT; infer_instance

theorem coordMisc_mono (co : Loc) (maxN : w32) (P P' Q Q' : Prop) (mtR fkR : Loc)
    (h1 : P → P') (h2 : Q → Q') :
    coordMisc (GF := GF) co maxN P Q mtR fkR ⊢ coordMisc co maxN P' Q' mtR fkR := by
  unfold coordMisc
  iintro ⟨%mst, %mat, %fkc, %mt, %fk, Hn, Hs, Ha, Hf, Hmt, Hfk, %Hmt0, Hmtm, Hfkc, %Hq⟩
  iexists mst, mat, fkc, mt, fk
  iframe Hn Hs Ha Hf Hmt Hfk Hfkc
  isplitl []
  · ipureintro; exact Hmt0
  isplitl [Hmtm]
  · cases mt.lookup (W64 0) with
    | none => icases Hmtm with %Hp; ipureintro; exact h1 Hp
    | some p => iexact Hmtm
  ipureintro; exact h2 Hq

/-- `MaxTags[0]`'s cell: the coordinator's `maxAppliedTag` (owned) or a persistent tag. -/
theorem mtCell_acc (p0 A : Loc) (mat : src.gryffproto.Tag) :
    ((⌜p0 = A⌝ ∨ ∃ gt : src.gryffproto.Tag, p0 ↦□ gt) ∗ A ↦ mat : IProp GF) ⊢
      ∃ (dq : DFrac) (gt0 : src.gryffproto.Tag), p0 ↦{dq} gt0 ∗
        (p0 ↦{dq} gt0 -∗ A ↦ mat ∗ (⌜p0 = A⌝ ∨ ∃ gt : src.gryffproto.Tag, p0 ↦□ gt)) := by
  iintro ⟨(%Hp | ⟨%gt, #Hgt⟩), Ha⟩
  · subst Hp
    iexists DFrac.own 1, mat
    iframe Ha
    iintro Ha
    iframe Ha
    ileft; ipureintro; rfl
  · iexists DFrac.discard, gt
    iframe Hgt Ha
    iintro -
    iright; iexists gt; iframe Hgt

theorem wops_ne_nil {V : Type} (l : AMap 64 V) (k : w64) (v : V) (h : l.get? k = some v) :
    l ≠ [] := by
  rintro rfl; cases h

/-- The write op after the reply's counters (`numWrite2Replies++`, `numWrite2Applies++`). -/
theorem w2_wo (ρ : Repl2Names) (co p : Loc) (g : src.gryffcommon.WriteOp) (op : src.gryffcommon.Op)
    (wr : Loc) (gd : src.gryffproto.Dep) (gt : src.gryffproto.Tag) (w : WriteOp) (applied : w32)
    (wt : model.Tag) (hwt : w.writeTag = some wt) (hgt : tagOf gt = wt)
    (hg : op.RequestId' = w.requestId ∧ op.ClientId' = w.clientId ∧ op.Key' = W64 0 ∧ g.N' = w.n ∧
      depOf gd = w.dep ∧ g.WriteValue' = w.writeValue ∧ g.ForceWrite' = W32 1 ∧
      g.numWrite1Applies' = w.numWrite1Applies ∧ g.numWrite1Replies' = w.numWrite1Replies ∧
      g.numWrite2Applies' = w.numWrite2Applies ∧ g.numWrite2Replies' = w.numWrite2Replies ∧
      g.sentWrite2Round' = w.sentWrite2Round ∧ g.startedShortcircuitTimeout' = false) :
    writerIs (GF := GF) ρ w.clientId wr ∗
      p ↦ { g with numWrite2Replies' := g.numWrite2Replies' + W64 1,
                   numWrite2Applies' := if model.sgt applied 0 then g.numWrite2Applies' + W64 1
                                        else g.numWrite2Applies' } ∗
      g.Op' ↦ op ∗ op.Dep' ↦□ gd ∗
      (⌜g.MaxAppliedTag' = co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"]⌝ ∨
        ∃ gt : src.gryffproto.Tag, g.MaxAppliedTag' ↦□ gt) ∗
      optVtRep g.maxValTag' (some w.maxValTag) ∗ g.WriteTag' ↦□ gt ⊢
    writeOpRep ρ co p (w2Upd w applied) := by
  obtain ⟨Hg1, Hg2, Hg3, Hg4, Hg5, Hg6, Hg7, Hg8, Hg9, Hg10, Hg11, Hg12, Hg13⟩ := hg
  iintro ⟨#Hwr, Hp, Hop, #Hgd, Hmat, Hmvt, #Hgt⟩
  iapply (writeOpRep_open ρ co p _).2
  simp only [w2Upd]
  iexists _, op, wr, gd
  iframe Hwr Hp Hop Hgd Hmat Hmvt
  rw [hwt]
  isplitl []
  · iexists gt; iframe Hgt; ipureintro; exact hgt
  ipureintro
  refine ⟨Hg1, Hg2, Hg3, Hg4, Hg5, Hg6, Hg7, Hg8, Hg9, ?_, by simp [Hg11], Hg12, Hg13⟩
  simp only [Hg10]
  split <;> rfl

/-- The state with the write op at `id` updated in place. -/
def sMid (s : RState) (id : w64) (w' : WriteOp) : RState := { s with wops := s.wops.put id w' }

/-- Close `coordOwn` with the write op at `id` updated in place. -/
theorem coordOwn_close_wput (ρ : Repl2Names) (co : Loc) (ic : GoInterface) (k : Fin 3)
    (s : RState) (ropsR wopsR orR mtR fkR : Loc) (arS : GoSlice) (wm : GMap w64 Loc) (id : w64)
    (p : Loc) (w' : WriteOp) (hp : wm !! id = some p)
    (hdom : ∀ key, (wm.lookup key).isSome = (s.wops.get? key).isSome) (hrk : ropsKeyed s.rops) :
    coordFix (GF := GF) co ic k ropsR wopsR orR mtR fkR arS ∗
      coordMisc co s.maxN (s.wops.put id w' = [])
        (((s.wops.put id w').map (fun e => e.1.toNat)).Pairwise (· < ·)) mtR fkR ∗
      amapRep ropsR s.rops (fun p r => readOpRep ρ p r) ∗ amapRep orR s.ongoingReqs ongoingOpRep ∗
      wopsR ↦$ wm ∗ amapEnts s.wops (GMap.delete id wm) (fun p w => writeOpRep ρ co p w) ∗
      writeOpRep ρ co p w' ⊢
    coordOwn ρ co ic k { s with wops := s.wops.put id w' } := by
  iintro ⟨#Hfix, Hmisc, Hr, Ho, Hwm, Hwents, Hwo⟩
  iapply (coordOwn_open ρ co ic k _).2
  iexists ropsR, wopsR, orR, mtR, fkR, arS
  iframe Hfix Hmisc Hr Ho %hrk
  iapply (amapRep_open wopsR _ _).2
  iexists wm
  iframe Hwm
  isplitl []
  · ipureintro; intro key
    rw [amap_put_get]
    by_cases hk : key = id
    · subst hk; change (wm !! key).isSome = _; rw [hp, if_pos rfl]; rfl
    · rw [if_neg hk]; exact hdom key
  iapply amapEnts_update _ _ _ _ p _ hp
  iframe Hwents Hwo

attribute [-instance] go.InterfaceSemantics.method_interface_ok in
theorem GryffCoordinator.HandleWrite2Reply.wp_proof (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3) (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
    (m : model.Write2ReplyM) (rep : w32) (tp : Loc)
    (hstep : model.stepR k s (.msg (.write2Reply m)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) }}
      (App (App (App (App (App (coordM co go!"HandleWrite2Reply")
        (Val #(model.shiftInts m.requestId m.clientId))) (Val #rep)) (Val #tp))
        (Val #m.clientId)) (Val #m.applied))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }} := by
  have hcase := stepWrite2Reply_inv k s s' m outs hstep
  simp only [coordM]
  wp_start as ⟨Hc, #Hic, HC⟩
  ihave Hparts := (show icoordOk ρ ic k C ⊢ _ from by unfold icoordOk; exact .rfl) $$ Hic
  simp only [specT]
  icases Hparts with ⟨-, -, -, -, -, #HCW, -, #HPr, #HSt, -, -, -⟩
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
    wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
    subst Hst'
    wp_apply StatsMap.IncrementStrInt.wp' $$ [Hstats] as %_ -
    · stats_key
    · iframe Hstats
    wp_join iprop(∃ g2 : src.gryffcommon.WriteOp, write_ptr ↦ p ∗ p ↦ g2 ∗
        ⌜g2 = { g with numWrite2Replies' := g.numWrite2Replies' + W64 1,
                       numWrite2Applies' := if model.sgt m.applied 0 then g.numWrite2Applies' + W64 1
                                            else g.numWrite2Applies' }⌝) with [Hp write] as ⟨%g2, write, Hp, %Hgs⟩
    · iexists _
      iframe Hp write
      ipureintro
      have : model.sgt m.applied 0 = true := by
        simpa [model.sgt, model.slt] using Hif
      simp [this] <;> exact this
    · iexists _
      iframe Hp write
      ipureintro
      have : model.sgt m.applied 0 = false := by
        simpa [model.sgt, model.slt] using Hif
      simp [this] <;> exact this
    wp_printf HPr
    have h2 : BitVec.sdiv (W64 3) (W64 2) + W64 1 = model.NHALF + 1 := by decide
    rw [h2]
    have hR : g2.numWrite2Replies' = (w2Upd w m.applied).numWrite2Replies := by
      simp [Hgs, w2Upd, Hg11]
    have hA : g2.numWrite2Applies' = (w2Upd w m.applied).numWrite2Applies := by
      simp [Hgs, w2Upd, Hg10]
    rw [hR]
    wp_if_destruct
    · rcases hcase with ⟨-, wt, s2, outs2, hwt, hsc, rfl, rfl⟩ | ⟨hq, -⟩
      rotate_left
      · exfalso; simp only [model.sge, model.sle, _root_.decide_eq_false_iff_not] at hq
        exact hq Hif
      wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
      subst Hst'
      wp_apply StatsMap.Increment.wp' $$ [Hstats] as %_ -
      · stats_key
      · iframe Hstats
      have hOp : g2.Op' = g.Op' := by rw [Hgs]
      rw [hOp]
      wp_auto
      rw [Hg3]
      wp_auto
      wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
      subst Hst'
      wp_apply StatsMap.Increment.wp' $$ [Hstats] as %_ -
      · stats_key
      · iframe Hstats
      rw [hwt]
      icases Hwt with ⟨%gt, #Hgt, %Hgtt⟩
      unfold coordMisc
      icases Hmisc with ⟨%mst, %mat, %fkc, %mt, %fk, Hn, Hs, Ha, Hf, Hmt, Hfk, %Hmt0, Hmtm, Hfkc, %Hsrt⟩
      have hWT : g2.WriteTag' = g.WriteTag' := by rw [Hgs]
      rw [hWT]
      wp_auto
      wp_apply Tag.wp_LessThan $$ [$Ha] as Ha
      wp_join iprop(∃ mat' : src.gryffproto.Tag, write_ptr ↦ p ∗ c_ptr ↦ co ∗ p ↦ g2 ∗
          co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"] ↦ mat') at next
        with [Ha write c Hp] as ⟨%mat', write, c, Hp, Ha⟩
      · cases (tagOf mat).lt (tagOf gt) <;> wp_auto <;> (try (rw [hWT]; wp_auto)) <;> wp_join_done
      have hN : g2.N' = g.N' := by rw [Hgs]
      have hWV : g2.WriteValue' = g.WriteValue' := by rw [Hgs]
      rw [hWT]
      wp_auto
      rw [hOp]
      wp_auto
      rw [Hg3]
      rcases hp0 : mt.lookup (W64 0) with _ | p0
      · simp only [hp0]
        icases Hmtm with %Hnil
        exact absurd Hnil (wops_ne_nil _ _ _ Hw)
      simp only [hp0]
      wp_apply wp_map_lookup1 $$ Hmt as Hmt
      rw [show mt !! W64 0 = some p0 from hp0]
      simp only [Option.getD_some]
      icases mtCell_acc p0 _ mat' $$ [Hmtm Ha] with ⟨%dq0, %gt0, Hp0, Hp0back⟩
      · iframe Hmtm Ha
      wp_apply Tag.wp_LessThan $$ [$Hp0] as Hp0
      ihave Hp0b := Hp0back $$ Hp0
      icases Hp0b with ⟨Ha, Hmtm⟩
      wp_join iprop(∃ mt' : GMap w64 Loc, write_ptr ↦ p ∗ c_ptr ↦ co ∗ p ↦ g2 ∗ g.Op' ↦ op ∗
          clientId_ptr ↦ m.clientId ∗ id_ptr ↦ model.shiftInts m.requestId m.clientId ∗
          mtR ↦$ mt' ∗ ⌜∀ kk, kk ≠ W64 0 → mt'.lookup kk = none⌝ ∗
          (∃ p1, ⌜mt'.lookup (W64 0) = some p1⌝ ∗
            (⌜p1 = co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"]⌝ ∨
              ∃ gt : src.gryffproto.Tag, p1 ↦□ gt))) at next
        with [write c Hp Hop clientId id Hmt Hmtm]
        as ⟨%mt', write, c, Hp, Hop, clientId, id, Hmt, %Hmt0', %p1, %Hp1, Hmtm⟩
      · cases (tagOf gt0).lt (tagOf gt)
        · wp_auto
          wp_join_done
          iexists mt
          iframe write c Hp Hop clientId id Hmt
          isplitl []
          · ipureintro; exact Hmt0
          iexists p0
          iframe Hmtm
          ipureintro; exact hp0
        · wp_auto
          rw [hOp, hWT]
          wp_auto
          rw [Hg3]
          wp_apply wp_mapInsert $$ Hmt as Hmt
          rw [hOp]
          wp_auto
          rw [hOp]
          wp_auto
          rw [Hg3]
          wp_apply wp_map_lookup1 $$ Hmt as Hmt
          wp_printf HPr
          isplitl []
          · ipureintro; rfl
          iexists _
          iframe write c Hp Hop clientId id Hmt
          isplitl []
          · ipureintro; intro kk hk
            change (<[W64 0 := g.WriteTag']> mt) !! kk = none
            rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]; exact Hmt0 kk hk
          iexists g.WriteTag'
          isplitl []
          · ipureintro; exact GMap.lookup_insert _ _ _
          iright; iexists gt; iframe Hgt
      ihave Hmisc : (coordMisc co s.maxN
          (s.wops.put (model.shiftInts m.requestId m.clientId) (w2Upd w m.applied) = [])
          (((s.wops.put (model.shiftInts m.requestId m.clientId) (w2Upd w m.applied)).map
            (fun e => e.1.toNat)).Pairwise (· < ·)) mtR fkR : IProp GF)
          $$ [Hn Hs Ha Hf Hmt Hfk Hmtm Hfkc]
      · unfold coordMisc
        iexists mst, mat', fkc, mt', fk
        iframe Hn Hs Ha Hf Hmt Hfk Hfkc
        isplitl []
        · ipureintro; exact Hmt0'
        isplitl [Hmtm]
        · rw [Hp1]; iexact Hmtm
        ipureintro; exact wops_sorted_put _ _ _ Hsrt
      rw [hA, h2]
      wp_join iprop(∃ (s3 : RState) (o3 : List Out), scPost ρ ropsR orR s3 ∗
          C s.storeVT ([.ext (.writeReply w.clientId w.requestId 1)] ++ o) ∗
          write_ptr ↦ p ∗ c_ptr ↦ co ∗ p ↦ g2 ∗
          ⌜(if model.sge (w2Upd w m.applied).numWrite2Applies (model.NHALF + 1) = true
            then model.shortCircuit s w.n (model.ValTag.mk w.writeValue wt) false
            else some (s, [])) = some (s3, o3)⌝)
        with [Hr Ho HC write c Hp] as ⟨%s3, %o3, Hpost, HC, write, c, Hp, %Hs3⟩
      · have hq : model.sge (w2Upd w m.applied).numWrite2Applies (model.NHALF + 1) = true := by
          simpa [model.sge, model.sle] using Hif
        have hsc1 := hsc
        rw [hq] at hsc1
        simp only [↓reduceIte] at hsc1
        wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
        subst Hst'
        wp_apply StatsMap.Increment.wp' $$ [Hstats] as %_ -
        · stats_key
        · iframe Hstats
        rw [hN, hWV, hWT]
        wp_auto
        ipersist «$a1»
        have hv : vtOf { V' := g.WriteValue', T' := gt } = model.ValTag.mk w.writeValue wt := by
          simp only [vtOf, Hg6, Hgtt]
        rw [← hv] at hsc1
        rw [Hg4]
        wp_apply (GryffCoordinator.ShortCircuit.wp_int ρ co ic k C s _ outs2
          ([.ext (.writeReply w.clientId w.requestId 1)] ++ o) s.storeVT w.n «$a1_ptr» _ false
          ropsR wopsR orR mtR fkR arS hsc1 Hrk) $$ [Hr Ho HC] as ⟨Hpost, HC⟩
        · iframe Hfix Hr Ho Hic «$a1»
          rw [List.append_assoc] at *
          iframe HC
        isplitl []
        · ipureintro; rfl
        iexists _, outs2
        iframe Hpost HC write c Hp
        ipureintro
        rw [hq]
        simp only [↓reduceIte]
        rw [hv] at hsc1
        exact hsc1
      · have hq : model.sge (w2Upd w m.applied).numWrite2Applies (model.NHALF + 1) = false := by
          simpa [model.sge, model.sle] using Hif
        have hsc1 := hsc
        rw [hq] at hsc1
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hsc1
        obtain ⟨hs2, ho2⟩ := hsc1
        subst hs2 ho2
        wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
        subst Hst'
        wp_apply StatsMap.Increment.wp' $$ [Hstats] as %_ -
        · stats_key
        · iframe Hstats
        isplitl []
        · ipureintro; rfl
        iexists s, []
        unfold scPost
        iframe Hr Ho write c Hp
        rw [hq]
        simp only [List.nil_append, Bool.false_eq_true, ↓reduceIte]
        iframe HC
      have hs3 : s3 = s2 := by
        rw [hsc] at Hs3; exact (Prod.mk.inj (Option.some.inj Hs3)).1.symm
      subst hs3
      have hfr : s3 = { s with rops := s3.rops, ongoingReqs := s3.ongoingReqs } := by
        split at hsc
        · exact sc.shortCircuit_frame _ _ _ _ _ _ hsc
        · cases hsc; rfl
      have hrk3 : ropsKeyed s3.rops := by -- H1b-R1
        split at hsc
        · exact shortCircuit_ropsKeyed _ _ _ _ _ _ hsc Hrk
        · cases hsc; exact Hrk
      wp_apply wp_mapDelete $$ Hwm as Hwm
      rw [hN, Hg4]
      unfold scPost
      icases Hpost with ⟨Hr, Ho⟩
      icases (amapRep_open orR _ _).1 $$ Ho with ⟨%om, Hom, %Hodom, Hoents⟩
      wp_apply wp_mapDelete $$ Hom as Hom
      rw [hOp]
      wp_auto
      rw [hOp]
      wp_auto
      rw [Hg1, Hg2]
      rw [List.singleton_append]
      wp_apply HCW $$ %w.requestId %w.clientId %s.storeVT %o %wr [HC] as %_ ⟨%_, HC⟩
      · iframe HC Hwr
      iapply HΦ
      rw [hfr]
      simp only [model.RState.storeVT]
      iframe HC
      iapply (coordOwn_open ρ co ic k _).2
      iexists ropsR, wopsR, orR, mtR, fkR, arS
      dsimp only
      iframe Hfix Hr %hrk3
      isplitl [Hmisc]
      · iapply coordMisc_mono _ _ _ _ _ _ _ _
          (fun h => absurd h (amap_put_ne_nil _ _ _))
          (fun h => by
            rw [← amap_put_del _ _ (w2Upd w m.applied)]
            exact List.Pairwise.sublist (List.filter_sublist.map _) h)
          $$ Hmisc
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
        by_cases hk : key = w.n
        · subst hk; rw [GMap.lookup_delete, amap_del_get_self]; rfl
        · rw [GMap.lookup_delete_ne _ (Ne.symm hk), amap_del_get_ne _ _ _ hk]; exact Hodom key
      iapply amapEnts_drop $$ Hoents
    · rcases hcase with ⟨hq, -⟩ | ⟨-, rfl, rfl⟩
      · exfalso; simp only [model.sge, model.sle, _root_.decide_eq_true_eq] at hq
        exact Hif hq
      subst Hgs
      iapply HΦ
      simp only [model.RState.storeVT, List.nil_append]
      iframe HC
      iapply (coordOwn_open ρ co ic k _).2
      iexists ropsR, wopsR, orR, mtR, fkR, arS
      dsimp only
      iframe Hfix Hr Ho %Hrk
      isplitl [Hmisc]
      · iapply coordMisc_mono _ _ _ _ _ _ _ _
          (fun h => absurd h (wops_ne_nil _ _ _ Hw)) (wops_sorted_put _ _ _) $$ Hmisc
      iapply (amapRep_open wopsR _ _).2
      iexists wm
      iframe Hwm
      isplitl []
      · ipureintro; intro key
        rw [amap_put_get]
        by_cases hk : key = model.shiftInts m.requestId m.clientId
        · subst hk; rw [hg, if_pos rfl]; rfl
        · rw [if_neg hk]; exact Hwdom key
      iapply amapEnts_update _ _ _ _ p _ hg
      iframe Hwents
      iapply (writeOpRep_open ρ co p _).2
      simp only [w2Upd]
      iexists _, op, wr, gd
      iframe Hwr Hp Hop Hgd Hmat Hmvt Hwt
      ipureintro
      exact ⟨Hg1, Hg2, Hg3, Hg4, Hg5, Hg6, Hg7, Hg8, Hg9, Hg10 ▸ rfl, Hg11 ▸ rfl, Hg12, Hg13⟩

end

end Perennial.gryff.replica2

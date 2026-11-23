/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/CoordRead1.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1: the coordinator's `HandleRead1Reply`.
-/
module

public import Dsverify.Proof.gryff.H1.CoordStartDefs
public import Dsverify.Proof.gryff.H1.PureRead1
public import Dsverify.Proof.gryff.H1.Pure
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


/-- `readOpRep` with the capacity of `replicasWithMaxTag` (`HandleRead1Reply` appends to it). -/
theorem readOpRep_openC (ρ : Repl2Names) (p : Loc) (r : ReadOp) :
    readOpRep ρ p r ⊢ ∃ (g : src.gryffcommon.ReadOp) (o : src.gryffcommon.Op) (rws : List w32)
      (w : Loc) (gd : src.gryffproto.Dep),
    writerIs (GF := GF) ρ r.clientId w ∗ p ↦ g ∗ o.Dep' ↦□ gd ∗
    g.Op' ↦ o ∗ optVtRep g.maxValTag' r.maxValTag ∗ optVtRep g.ReadValTag' r.readValTag ∗
    g.replicasWithMaxTag' ↦* rws ∗ ownSliceCap w32 g.replicasWithMaxTag' (DFrac.own 1) ∗
    ⌜o.RequestId' = r.requestId ∧ o.ClientId' = r.clientId ∧ o.Key' = W64 0 ∧ g.N' = r.n ∧
      g.numRead1Replies' = r.numRead1Replies ∧ g.numRead2Replies' = r.numRead2Replies ∧
      g.readsWithMaxTag' = r.readsWithMaxTag ∧ g.sentRead2Round' = r.sentRead2Round ∧
      g.determinedReadVal' = r.determinedReadVal ∧ rws = r.replicasWithMaxTag⌝ := by
  exact (readOpRep_open ρ p r).1

theorem r1_if_pos {c : Prop} [Decidable c] (h : c) {α : Sort _} {t e : α} :
    (if c then t else e) = t := by
  simp [h]

/-- The read op's fields the max-tag update keeps. -/
def r1Ag (g g' : src.gryffcommon.ReadOp) : Prop :=
  g'.Op' = g.Op' ∧ g'.N' = g.N' ∧ g'.ReadValTag' = g.ReadValTag' ∧
  g'.numRead2Replies' = g.numRead2Replies' ∧ g'.sentRead2Round' = g.sentRead2Round' ∧
  g'.determinedReadVal' = g.determinedReadVal'

theorem r1S_storeVT_new (s : RState) (read : ReadOp) (m : model.Read1ReplyM)
    (h : r1New read m = true) : (r1S s read m).storeVT = ovw s.storeVT m.vt.v m.vt.t := by
  simp only [r1S, h, ↓reduceIte]
  obtain ⟨h1, h2, -⟩ := ovw_overwrite s m.vt.v m.vt.t
  simp only [model.RState.storeVT] at *
  rw [h1, h2]

theorem r1Put_storeVT (s : RState) (read : ReadOp) (m : model.Read1ReplyM) (X : ReadOp) :
    (r1Put s read m X).storeVT = (r1S s read m).storeVT := rfl

theorem r1Del_storeVT (s : RState) (read : ReadOp) (m : model.Read1ReplyM) (n : w32) :
    (r1Del s read m n).storeVT = (r1S s read m).storeVT := rfl

theorem r1S_old (s : RState) (read : ReadOp) (m : model.Read1ReplyM)
    (h : r1New read m = false) : r1S s read m = s := by
  simp [r1S, h]

theorem r1S_coord (s : RState) (read : ReadOp) (m : model.Read1ReplyM) :
    (r1S s read m).maxN = s.maxN ∧ (r1S s read m).rops = s.rops ∧
      (r1S s read m).wops = s.wops ∧ (r1S s read m).ongoingReqs = s.ongoingReqs := by
  unfold r1S model.RState.overwrite
  split
  · split <;> exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- Close `readOpRep` with a non-nil `maxValTag`. -/
theorem readOpRep_mk (ρ : Repl2Names) (p : Loc) (X : ReadOp) (g : src.gryffcommon.ReadOp)
    (op : src.gryffcommon.Op) (w : Loc) (gd : src.gryffproto.Dep) (gm : src.gryffproto.ValTag)
    (hX : X.maxValTag = some (vtOf gm) ∧ op.RequestId' = X.requestId ∧ op.ClientId' = X.clientId ∧
      op.Key' = W64 0 ∧ g.N' = X.n ∧ g.numRead1Replies' = X.numRead1Replies ∧
      g.numRead2Replies' = X.numRead2Replies ∧ g.readsWithMaxTag' = X.readsWithMaxTag ∧
      g.sentRead2Round' = X.sentRead2Round ∧ g.determinedReadVal' = X.determinedReadVal) :
    writerIs (GF := GF) ρ X.clientId w ∗ p ↦ g ∗ op.Dep' ↦□ gd ∗ g.Op' ↦ op ∗ g.maxValTag' ↦□ gm ∗
      optVtRep g.ReadValTag' X.readValTag ∗ g.replicasWithMaxTag' ↦* X.replicasWithMaxTag ∗
      ownSliceCap w32 g.replicasWithMaxTag' (DFrac.own 1) ⊢ readOpRep ρ p X := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hX
  iintro ⟨#Hwr, Hp, #Hdep, Hop, #Hgm, Hrv, Hrws, Hrwc⟩
  iapply (readOpRep_open ρ p X).2
  iexists g, op, X.replicasWithMaxTag, w, gd
  iframe Hwr Hp Hdep Hop Hrv Hrws Hrwc
  isplitl []
  · unfold optVtRep
    rw [h0]
    iexists gm
    iframe Hgm
    ipureintro; rfl
  ipureintro
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, rfl⟩

/-- `readOpRep_mk` with the field locations named (`opL`, `mxL`, `rvL`, `rwL`). -/
theorem readOpRep_mk2 (ρ : Repl2Names) (p : Loc) (X : ReadOp) (g : src.gryffcommon.ReadOp)
    (op : src.gryffcommon.Op) (w : Loc) (gd : src.gryffproto.Dep) (gm : src.gryffproto.ValTag)
    (cid : w32) (opL mxL rvL : Loc) (rwL : GoSlice) (rv0 : Option model.ValTag) (rs0 : List w32)
    (hL : g.Op' = opL ∧ g.maxValTag' = mxL ∧ g.ReadValTag' = rvL ∧ g.replicasWithMaxTag' = rwL ∧
      X.clientId = cid ∧ X.readValTag = rv0 ∧ X.replicasWithMaxTag = rs0)
    (hX : X.maxValTag = some (vtOf gm) ∧ op.RequestId' = X.requestId ∧ op.ClientId' = X.clientId ∧
      op.Key' = W64 0 ∧ g.N' = X.n ∧ g.numRead1Replies' = X.numRead1Replies ∧
      g.numRead2Replies' = X.numRead2Replies ∧ g.readsWithMaxTag' = X.readsWithMaxTag ∧
      g.sentRead2Round' = X.sentRead2Round ∧ g.determinedReadVal' = X.determinedReadVal) :
    writerIs (GF := GF) ρ cid w ∗ p ↦ g ∗ op.Dep' ↦□ gd ∗ opL ↦ op ∗ mxL ↦□ gm ∗
      optVtRep rvL rv0 ∗ rwL ↦* rs0 ∗ ownSliceCap w32 rwL (DFrac.own 1) ⊢ readOpRep ρ p X := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hL
  rw [← e1, ← e2, ← e3, ← e4, ← e5, ← e6, ← e7]
  exact readOpRep_mk ρ p X g op w gd gm hX

/-- Close `coordOwn` with the read op stored back (`r1Put`). -/
theorem coordOwn_close_r1 (ρ : Repl2Names) (co : Loc) (ic : GoInterface) (k : Fin 3)
    (s : RState) (read : ReadOp) (m : model.Read1ReplyM) (X : ReadOp)
    (ropsR wopsR orR mtR fkR : Loc) (arS : GoSlice) (rm : GMap w64 Loc) (p : Loc)
    (hp : rm !! model.shiftInts m.requestId m.clientId = some p)
    (hdom : ∀ key, (rm !! key).isSome = (s.rops.get? key).isSome) (hrk : ropsKeyed s.rops)
    (hX : model.shiftInts m.requestId m.clientId = model.shiftInts X.requestId X.clientId) :
    coordFix co ic k ropsR wopsR orR mtR fkR arS ∗
      coordMisc co s.maxN (s.wops = []) ((s.wops.map (fun e => e.1.toNat)).Pairwise (· < ·)) mtR fkR ∗
      amapRep (GF := GF) wopsR s.wops (fun p w => writeOpRep ρ co p w) ∗ amapRep orR s.ongoingReqs ongoingOpRep ∗
      ropsR ↦$ rm ∗
      amapEnts s.rops (GMap.delete (model.shiftInts m.requestId m.clientId) rm)
        (fun p r => readOpRep ρ p r) ∗
      readOpRep ρ p X ⊢ coordOwn ρ co ic k (r1Put s read m X) := by
  iintro ⟨#Hfix, Hmisc, Hw, Ho, Hrm, Hrents, Hro⟩
  obtain ⟨c1, c2, c3, c4⟩ := r1S_coord s read m
  iapply (coordOwn_open ρ co ic k _).2
  iexists ropsR, wopsR, orR, mtR, fkR, arS
  simp only [r1Put]
  rw [c1, c2, c3, c4]
  iframe Hfix Hmisc Hw Ho
  isplitl []
  · ipureintro; exact ropsKeyed_put _ _ _ hrk hX
  iapply (amapRep_open ropsR _ _).2
  iexists rm
  iframe Hrm
  isplitl []
  · ipureintro; intro key
    rw [amap_put_get]
    by_cases hk : key = model.shiftInts m.requestId m.clientId
    · subst hk; rw [hp, if_pos rfl]; rfl
    · rw [if_neg hk]; exact hdom key
  iapply amapEnts_update _ _ _ _ p _ hp
  iframe Hrents Hro

/-- Reopen a read op to set `sentRead2Round` (`r2Z`). -/
theorem readOpRep_upd (ρ : Repl2Names) (p : Loc) (c : ReadOp) :
    readOpRep (GF := GF) ρ p (r2Y c) ⊢ ∃ g : src.gryffcommon.ReadOp, p ↦ g ∗
      (p ↦ { g with sentRead2Round' := true } -∗ readOpRep ρ p (r2Z c)) := by
  iintro Hro
  icases (readOpRep_open ρ p _).1 $$ Hro with
    ⟨%g, %op, %rws, %w, %gd, #Hwr, Hp, #Hdep, Hop, Hmx, Hrv, Hrws, Hrwc, %Hgf⟩
  iexists g
  iframe Hp
  iintro Hp
  iapply (readOpRep_open ρ p _).2
  dsimp only [r2Z]
  iexists _, op, rws, w, gd
  iframe Hwr Hp Hdep Hop Hmx Hrv Hrws Hrwc
  ipureintro
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := Hgf
  exact ⟨h1, h2, h3, h4, h5, h6, h7, rfl, h9, h10⟩

set_option hygiene false in
/-- A `Printf` whose `[]interface{}` literal holds struct values (`Tag`s). -/
macro "wp_printfT " H:ident : tactic => `(tactic| (
  wp_bind (App (Val (GoInstruction (CompositeLiteral _))) _)
  iapply wp_slice_literal (V := GoInterface) (t := go.any) _ _
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %_sl ⟨-, -⟩
  wp_pures
  try (wp_load; wp_pures; wp_load)
  wp_apply $H:ident $$ %_ %_ as %_ ⟨%_, -⟩))

set_option maxHeartbeats 1600000 in
attribute [-instance] go.InterfaceSemantics.method_interface_ok in
theorem GryffCoordinator.HandleRead1Reply.wp_proof (ρ : Repl2Names) (co : Loc) (ic : GoInterface)
    (k : Fin 3) (C : model.ValTag → List Out → IProp GF) (s s' : RState) (outs o : List Out)
    (m : model.Read1ReplyM) (vp : Loc) (gv : src.gryffproto.ValTag) (hv : vtOf gv = m.vt)
    (hid : s.id = rid32 k)
    (hstep : model.stepR k s (.msg (.read1Reply m)) = .ok (s', outs)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ coordOwn ρ co ic k s ∗
        icoordOk ρ ic k C ∗ C s.storeVT (outs ++ o) ∗ vp ↦□ gv }}
      (App (App (App (coordM co go!"HandleRead1Reply")
        (Val #(model.shiftInts m.requestId m.clientId))) (Val #vp)) (Val #m.replicaId))
    {{ RET #(); coordOwn ρ co ic k s' ∗ C s'.storeVT o }} := by
  have hcase := stepRead1Reply_inv k s s' m outs hstep
  simp only [coordM]
  wp_start as ⟨Hc, Hic, HC, #Hvp⟩
  unfold icoordOk
  simp only [specT]
  icases Hic with ⟨-, #HS2, -, -, #HCR, -, #HOv, #HPr, #HSt, -, -, -⟩
  icases (coordOwn_open ρ co ic k s).1 $$ Hc with
    ⟨%ropsR, %wopsR, %orR, %mtR, %fkR, %arS, #Hfix, Hmisc, %Hrk, Hr, Hw, Ho⟩
  icases (coordFix_open co ic k ropsR wopsR orR mtR fkR arS).1 $$ Hfix with ⟨#F1, #F2, #F3, #F4, #F5, #F6, #F7, #F8, #F9, #F10, #F11, #F12, #F13, #F14⟩
  icases (amapRep_open ropsR s.rops _).1 $$ Hr with ⟨%rm, Hrm, %Hrdom, Hrents⟩
  wp_auto
  wp_apply wp_map_lookup2 $$ Hrm as Hrm
  cases hg : rm !! model.shiftInts m.requestId m.clientId with
  | none =>
    have hgm : s.rops.get? (model.shiftInts m.requestId m.clientId) = none := by
      have := Hrdom (model.shiftInts m.requestId m.clientId); rw [hg] at this
      cases h : s.rops.get? (model.shiftInts m.requestId m.clientId) with
      | none => rfl
      | some _ => rw [h] at this; cases this
    rcases hcase with ⟨-, rfl, rfl⟩ | ⟨read, hr, -⟩
    rotate_left
    · rw [hgm] at hr; cases hr
    simp only [Option.isSome_none]
    wp_auto
    wp_printf0 HPr
    iapply HΦ
    simp only [List.nil_append]
    iframe HC
    iapply (coordOwn_open ρ co ic k _).2
    iexists ropsR, wopsR, orR, mtR, fkR, arS
    iframe Hfix Hmisc Hw Ho %Hrk
    iapply (amapRep_open ropsR _ _).2
    iexists rm
    iframe Hrm Hrents
    ipureintro; exact Hrdom
  | some p =>
    icases amapEnts_take _ _ _ _ p hg $$ Hrents with ⟨Hrents, ⟨%read, %Hread, Hro⟩⟩
    icases readOpRep_openC ρ p read $$ Hro with
      ⟨%g, %op, %rws, %w, %gd, #Hwr, Hp, #Hdep, Hop, Hmx, Hrv, Hrws, Hrwc, %Hgf⟩
    obtain ⟨Hrid, Hcid, Hkey, HN, H1, H2, H3, H4, H5, Hrws⟩ := Hgf
    rcases hcase with ⟨hn, -⟩ | ⟨read', hr', hcase⟩
    · rw [hn] at Hread; cases Hread
    rw [Hread] at hr'; cases hr'
    simp only [Option.isSome_some, Option.getD_some]
    wp_auto
    wp_join iprop(c_ptr ↦ co ∗ replicaId_ptr ↦ m.replicaId ∗ read_ptr ↦ p ∗ p ↦ g) at next
      with [c replicaId read Hp] as ⟨c, replicaId, read, Hp⟩
    · cases g.determinedReadVal'
      · try wp_auto
        wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
        subst Hst'
        wp_apply StatsMap.IncrementStrInt.wp' $$ [Hstats] as %_ -
        · stats_key
        · iframe Hstats
        wp_join_done
      · try wp_auto
        wp_join_done
    wp_printf HPr
    have hvt : tagOf gv.T' = m.vt.t := by rw [← hv]; rfl
    have hvv : gv.V' = m.vt.v := by rw [← hv]; rfl
    rw [Hrws]
    wp_join iprop(∃ (g' : src.gryffcommon.ReadOp) (gm' : src.gryffproto.ValTag),
        c_ptr ↦ co ∗ read_ptr ↦ p ∗ vt_ptr ↦ vp ∗ p ↦ g' ∗ g.Op' ↦ op ∗ g'.maxValTag' ↦□ gm' ∗
        g'.replicasWithMaxTag' ↦* (r1A s read m).replicasWithMaxTag ∗
        ownSliceCap w32 g'.replicasWithMaxTag' (DFrac.own 1) ∗
        C (r1S s read m).storeVT (outs ++ o) ∗
        ⌜(r1A s read m).maxValTag = some (vtOf gm') ∧
          g'.numRead1Replies' = (r1A s read m).numRead1Replies ∧
          g'.readsWithMaxTag' = (r1A s read m).readsWithMaxTag ∧ r1Ag g g'⌝) at next
      with [c read vt Hp Hop Hmx Hrws Hrwc HC]
      as ⟨%g', %gm', c, read, vt, Hp, Hop, #Hgm', Hrws, Hrwc, HC, %Hg'⟩
    · ihave #Hvp2 := Hvp
      iStructNamedPrefix Hvp "gv"
      unfold optVtRep
      cases hmx : read.maxValTag with
      | none =>
        icases Hmx with %Hmn
        have hnew : r1New read m = true := by simp [r1New, hmx]
        rw [Hmn]
        wp_auto
        wp_apply wp_slice_make2 (V := w32) as %sl0 ⟨Hsl0, Hcap0⟩
        · ipureintro; decide
        simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
        try wp_auto
        rw [Hkey]
        wp_apply HOv $$ %gv.V' %_ %gv.T' %s.storeVT %(outs ++ o) [HC] as %_ ⟨%_, HC⟩
        · iframe HC gvT
        try wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int32))))
          (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := w32) (t := go.int32) [rid32 k]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %sl_ptr ⟨Hsl, -⟩
        wp_apply wp_slice_append (V := w32) _ _ _ [rid32 k] (DFrac.own 1) $$ [$Hsl0 $Hcap0 $Hsl]
          as %r ⟨Hr, Hrcap, -⟩
        try wp_auto
        wp_join_done
        iexists _, gv
        iframe c read vt Hp Hop Hvp2
        rw [r1S_storeVT_new s read m hnew, ← hvv, ← hvt]
        iframe HC
        simp only [r1A, hnew, ↓reduceIte, hid, List.nil_append]
        iframe Hr Hrcap
        ipureintro
        refine ⟨by rw [hv], by rw [H1]; rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | some mx =>
        icases Hmx with ⟨%gm, #Hgm, %Hgmv⟩
        ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgm
        ihave #Hgm2 := Hgm
        iStructNamedPrefix Hgm "gm"
        have hmt : tagOf gm.T' = mx.t := by rw [← Hgmv]; rfl
        rw [decide_eq_false Hnn]
        wp_auto
        wp_apply Tag.wp_GreaterThan $$ [$gvT] as -
        rw [hvt, hmt]
        cases hgt : m.vt.t.gt mx.t
        · have hnew : r1New read m = false := by simp [r1New, hmx, hgt]
          try wp_auto
          wp_join_done
          iexists _, gm
          iframe c read vt Hp Hop Hgm2
          rw [r1S_old s read m hnew]
          iframe HC
          simp only [r1A, hnew, Bool.false_eq_true, ↓reduceIte]
          iframe Hrws Hrwc
          ipureintro
          refine ⟨by rw [hmx, Hgmv], by rw [H1]; rfl, H3, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · have hnew : r1New read m = true := by simp [r1New, hmx, hgt]
          try wp_auto
          wp_if_destruct
          · exfalso; apply Hnn; simpa using Hif
          wp_bind (App (Val (GoInstruction (CompositeLiteral _))) _)
          iapply wp_slice_literal (V := GoInterface) (t := go.any) _ _
          wp_auto
          isplitl []
          · ipureintro; rfl
          iintro %_sl ⟨-, -⟩
          wp_pures
          wp_printf0 HPr
          try wp_auto
          wp_apply wp_slice_make2 (V := w32) as %sl0 ⟨Hsl0, Hcap0⟩
          · ipureintro; decide
          simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
          try wp_auto
          rw [Hkey]
          wp_apply HOv $$ %gv.V' %_ %gv.T' %s.storeVT %(outs ++ o) [HC] as %_ ⟨%_, HC⟩
          · iframe HC gvT
          try wp_auto
          wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int32))))
            (Val (LiteralValueV _)))
          iapply wp_slice_literal (V := w32) (t := go.int32) [rid32 k]
          wp_auto
          isplitl []
          · ipureintro; rfl
          iintro %sl_ptr ⟨Hsl, -⟩
          wp_apply wp_slice_append (V := w32) _ _ _ [rid32 k] (DFrac.own 1) $$ [$Hsl0 $Hcap0 $Hsl]
            as %r ⟨Hr, Hrcap, -⟩
          try wp_auto
          wp_join_done
          iexists _, gv
          iframe c read vt Hp Hop Hvp2
          rw [r1S_storeVT_new s read m hnew, ← hvv, ← hvt]
          iframe HC
          simp only [r1A, hnew, ↓reduceIte, hid, List.nil_append]
          iframe Hr Hrcap
          ipureintro
          refine ⟨by rw [hv], by rw [H1]; rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨HA1, HA2, HA3, Ag1, Ag2, Ag3, Ag4, Ag5, Ag6⟩ := Hg'
    ihave #Hgq := Hgm'
    iStructNamedPrefix Hgq "gq"
    ihave #Hvp3 := Hvp
    iStructNamedPrefix Hvp3 "gv"
    wp_join iprop(∃ g'' : src.gryffcommon.ReadOp, c_ptr ↦ co ∗ read_ptr ↦ p ∗ p ↦ g'' ∗
        g''.replicasWithMaxTag' ↦* (r1B s read m).replicasWithMaxTag ∗
        ownSliceCap w32 g''.replicasWithMaxTag' (DFrac.own 1) ∗
        ⌜g''.readsWithMaxTag' = (r1B s read m).readsWithMaxTag ∧ g''.maxValTag' = g'.maxValTag' ∧
          g''.numRead1Replies' = g'.numRead1Replies' ∧ r1Ag g' g''⌝) at next
      with [c read replicaId Hp Hrws Hrwc] as ⟨%g'', c, read, Hp, Hrws, Hrwc, %Hg''⟩
    · wp_auto
      wp_if_destruct
      · have hT1 := Hif
        wp_if_destruct
        · have hT2 := Hif
          wp_if_destruct
          · have hT3 := Hif
            have heq : m.vt.t = (vtOf gm').t := by
              rw [← hvt]; simp only [vtOf, tagOf]; rw [hT1, hT2, hT3]
            wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int32))))
              (Val (LiteralValueV _)))
            iapply wp_slice_literal (V := w32) (t := go.int32) [m.replicaId]
            wp_auto
            isplitl []
            · ipureintro; rfl
            iintro %sl_ptr ⟨Hsl, -⟩
            wp_apply wp_slice_append (V := w32) _ _ _ [m.replicaId] (DFrac.own 1) $$ [$Hrws $Hrwc $Hsl]
              as %r ⟨Hr, Hrcap, -⟩
            try wp_auto
            wp_printfT HPr
            try wp_auto
            wp_join_done
            iexists _
            iframe c read Hp
            obtain ⟨hB1, hB2⟩ := r1B_eq s read m _ HA1 heq
            rw [hB2]
            iframe Hr Hrcap
            ipureintro
            exact ⟨by rw [hB1, ← HA3]; rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · have hne : m.vt.t ≠ (vtOf gm').t := fun h => Hif (congrArg model.Tag.rmwc (hvt.trans h))
            rw [r1B_ne s read m _ HA1 hne]
            wp_join_done
            iexists _
            iframe c read Hp Hrws Hrwc
            ipureintro; exact ⟨HA3, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · have hne : m.vt.t ≠ (vtOf gm').t := fun h => Hif (congrArg model.Tag.cid (hvt.trans h))
          rw [r1B_ne s read m _ HA1 hne]
          wp_join_done
          iexists _
          iframe c read Hp Hrws Hrwc
          ipureintro; exact ⟨HA3, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · have hne : m.vt.t ≠ (vtOf gm').t := fun h => Hif (congrArg model.Tag.ts (hvt.trans h))
        rw [r1B_ne s read m _ HA1 hne]
        wp_join_done
        iexists _
        iframe c read Hp Hrws Hrwc
        ipureintro; exact ⟨HA3, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨Hb1, Hb2, Hb3, Bg1, Bg2, Bg3, Bg4, Bg5, Bg6⟩ := Hg''
    obtain ⟨hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9⟩ := r1B_same s read m
    obtain ⟨hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8⟩ := r1A_ids s read m
    have hkey : model.shiftInts m.requestId m.clientId =
        model.shiftInts (r1B s read m).requestId (r1B s read m).clientId := by
      rw [hS1, hS2, hA1, hA2]; exact Hrk _ _ Hread
    have hnr : g''.numRead1Replies' = (r1B s read m).numRead1Replies := by rw [Hb3, HA2, hS6]
    have h2 : BitVec.sdiv (W64 3) (W64 2) + W64 1 = model.NHALF + 1 := by decide
    rw [hnr, h2]
    wp_if_destruct
    · have hq : model.sge (r1B s read m).numRead1Replies (model.NHALF + 1) = true := by
        simpa [model.sge, model.sle] using Hif
      rcases hcase with ⟨hq', -⟩ | ⟨-, hcase⟩
      · rw [hq] at hq'; cases hq'
      have hdB : (r1B s read m).determinedReadVal = g''.determinedReadVal' := by
        rw [hS9, hA7, Bg6, Ag6, H5]
      wp_join iprop(∃ g3 : src.gryffcommon.ReadOp, c_ptr ↦ co ∗ read_ptr ↦ p ∗ p ↦ g3 ∗
          optVtRep g3.ReadValTag' (r1C (r1B s read m)).readValTag ∗
          ⌜g3.determinedReadVal' = (r1C (r1B s read m)).determinedReadVal ∧
            g3.Op' = g''.Op' ∧ g3.N' = g''.N' ∧ g3.maxValTag' = g''.maxValTag' ∧
            g3.numRead1Replies' = g''.numRead1Replies' ∧ g3.numRead2Replies' = g''.numRead2Replies' ∧
            g3.readsWithMaxTag' = g''.readsWithMaxTag' ∧ g3.sentRead2Round' = g''.sentRead2Round' ∧
            g3.replicasWithMaxTag' = g''.replicasWithMaxTag'⌝)
        at next with [c read Hp Hrv] as ⟨%g3, c, read, Hp, Hrv, %Hg3⟩
      · cases hd : g''.determinedReadVal'
        · try wp_auto
          wp_join_done
          obtain ⟨hC1, hC2⟩ := r1C_f _ (hdB.trans hd)
          rw [hC1, hC2, hS4, HA1]
          iexists _
          iframe c read Hp
          unfold optVtRep
          dsimp only
          rw [Hb2]
          isplitl []
          · iexists gm'
            iframe Hgm'
            ipureintro; rfl
          ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · try wp_auto
          wp_join_done
          rw [r1C_t _ (hdB.trans hd), hS5, hA4]
          iexists g''
          iframe c read Hp
          rw [Bg3, Ag3]
          iframe Hrv
          ipureintro; exact ⟨hdB.symm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      obtain ⟨Hd3, G1, G2, G3, G4, G5, G6, G7, G8⟩ := Hg3
      obtain ⟨hC1, hC2, hC3, hC4, hC5, hC6, hC7, hC8, hC9⟩ := r1C_same (r1B s read m)
      have hrw3 : g3.readsWithMaxTag' = (r1C (r1B s read m)).readsWithMaxTag := by rw [G6, Hb1, hC7]
      have hOp3 : g3.Op' = g.Op' := by rw [G1, Bg1, Ag1]
      have hN3 : g3.N' = read.n := by rw [G2, Bg2, Ag2, HN]
      have hsr3 : g3.sentRead2Round' = (r1C (r1B s read m)).sentRead2Round := by
        rw [G7, Bg5, Ag5, H4, hC8, hS8, hA6]
      rw [hrw3, h2]
      wp_if_destruct
      · have hq2 : model.sge (r1C (r1B s read m)).readsWithMaxTag (model.NHALF + 1) = true := by
          simpa [model.sge, model.sle] using Hif
        rcases hcase with ⟨-, rv, hrv, rfl, rfl⟩ | ⟨hq', -⟩ | ⟨hq', -⟩
        rotate_left
        · rw [hq2] at hq'; cases hq'
        · rw [hq2] at hq'; cases hq'
        wp_printfT HPr
        wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
        subst Hst'
        wp_apply StatsMap.Increment.wp' $$ [Hstats] as %_ -
        · stats_key
        · iframe Hstats
        rw [hOp3]
        wp_auto
        rw [Hkey]
        wp_auto
        wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
        subst Hst'
        wp_apply StatsMap.Increment.wp' $$ [Hstats] as %_ -
        · stats_key
        · iframe Hstats
        icases (amapRep_open orR s.ongoingReqs _).1 $$ Ho with ⟨%om, Hom, %Hodom, Hoents⟩
        rw [hN3]
        wp_apply wp_mapDelete $$ Hom as Hom
        wp_apply wp_mapDelete $$ Hrm as Hrm
        unfold optVtRep
        rw [hrv]
        dsimp only
        icases Hrv with ⟨%gr, #Hgr, %Hgrv⟩
        iStructNamedPrefix Hgr "gr"
        try wp_auto
        repeat (first | (rw [hOp3]) | (rw [Hrid]) | (rw [Hcid]) | wp_auto)
        have hv : rv.v = gr.V' := by rw [← Hgrv]; rfl
        have hcl : (r1C (r1B s read m)).clientId = read.clientId := by rw [hC2, hS2, hA2]
        have hrq : (r1C (r1B s read m)).requestId = read.requestId := by rw [hC1, hS1, hA1]
        rw [hv, hcl, hrq, List.singleton_append] at *
        wp_apply HCR $$ %read.requestId %read.clientId %gr.V' %(r1S s read m).storeVT %o %w [HC]
          as %_ ⟨%_, HC⟩
        · iframe HC Hwr
        iapply HΦ
        obtain ⟨c1, c2, c3, c4⟩ := r1S_coord s read m
        have hn : (r1C (r1B s read m)).n = read.n := by rw [hC3, hS3, hA3]
        rw [hn, r1Del_storeVT]
        simp only [r1Del]
        isplitr [HC]
        · iapply (coordOwn_open ρ co ic k _).2
          iexists ropsR, wopsR, orR, mtR, fkR, arS
          rw [c1, c2, c3, c4]
          iframe Hfix Hmisc Hw
          isplitl []
          · ipureintro; exact ropsKeyed_del _ _ Hrk -- H1b-R1
          isplitl [Hrm Hrents]
          · iapply (amapRep_open ropsR _ _).2
            iexists (GMap.delete (model.shiftInts m.requestId m.clientId) rm)
            iframe Hrm
            isplitl []
            · ipureintro; intro key
              by_cases hk : key = model.shiftInts m.requestId m.clientId
              · subst hk; rw [GMap.lookup_delete, amap_del_get_self]; rfl
              · rw [GMap.lookup_delete_ne _ (Ne.symm hk), amap_del_get_ne _ _ _ hk]; exact Hrdom key
            iapply amapEnts_del $$ Hrents
          · iapply (amapRep_open orR _ _).2
            iexists (GMap.delete read.n om)
            iframe Hom
            isplitl []
            · ipureintro; intro key
              by_cases hk : key = read.n
              · subst hk; rw [GMap.lookup_delete, amap_del_get_self]; rfl
              · rw [GMap.lookup_delete_ne _ (Ne.symm hk), amap_del_get_ne _ _ _ hk]; exact Hodom key
            iapply amapEnts_drop $$ Hoents
        · iexact HC
      · have hq2 : model.sge (r1C (r1B s read m)).readsWithMaxTag (model.NHALF + 1) = false := by
          simpa [model.sge, model.sle] using Hif
        rw [hsr3]
        cases hsent : (r1C (r1B s read m)).sentRead2Round
        · rcases hcase with ⟨hq', -⟩ | ⟨-, hs', -⟩ | ⟨-, -, rv, hrv, hsend, hs'⟩
          · rw [hq2] at hq'; cases hq'
          · rw [hsent] at hs'; cases hs'
          have hZ : s' = r1Put s read m (r2Z (r1C (r1B s read m))) := hs'
          subst hZ
          try wp_auto
          wp_printfT HPr
          wp_apply wp_slice_make2 (V := w32) as %rsl0 ⟨Hrsl, Hrcap⟩
          · ipureintro; decide
          simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
          try wp_auto
          rw [← G8]
          ihave %Hlen := ownSlice_len $$ Hrws
          ihave HI : (∃ (iv : w32) (rsl : GoSlice), "i" ∷ i_ptr ↦ iv ∗ "replicas" ∷ replicas_ptr ↦ rsl ∗
              "Hrsl" ∷ rsl ↦* r2After (r1B s read m).replicasWithMaxTag iv ∗
              "Hrcap" ∷ ownSliceCap w32 rsl (DFrac.own 1) ∗ "c" ∷ c_ptr ↦ co ∗
              "read" ∷ read_ptr ↦ p ∗ "Hp" ∷ p ↦ g3 ∗
              "Hrws" ∷ g3.replicasWithMaxTag' ↦* (r1B s read m).replicasWithMaxTag ∗
              "%Hi" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ 3⌝ : IProp GF) $$ [i replicas Hrsl Hrcap c read Hp Hrws]
          · iexists W32 0, rsl0
            rw [show r2After (r1B s read m).replicasWithMaxTag (W32 0) = [] from rfl]
            iframe i replicas Hrsl Hrcap c read Hp Hrws
            ipureintro; decide
          wp_for HI
          wp_if_destruct
          · have hc : sint.Z iv < 3 := by word
            ihave HJ : (∃ jv : w64, "j" ∷ j_ptr ↦ jv ∗ "send" ∷ send_ptr ↦ true ∗
                "read" ∷ read_ptr ↦ p ∗ "Hp" ∷ p ↦ g3 ∗
                "Hrws" ∷ g3.replicasWithMaxTag' ↦* (r1B s read m).replicasWithMaxTag ∗
                "%Hj" ∷ ⌜0 ≤ sint.Z jv ∧ sint.nat jv ≤ (r1B s read m).replicasWithMaxTag.length ∧
                  ((r1B s read m).replicasWithMaxTag.take (sint.nat jv)).contains iv = false⌝ : IProp GF)
              $$ [j send read Hp Hrws]
            · iexists W64 0
              iframe j send read Hp Hrws
              ipureintro
              refine ⟨by decide, by simp [sint.nat], by simp [sint.nat]⟩
            wp_for HJ
            obtain ⟨Hj0, Hjl, Hjc⟩ := Hj
            wp_if_destruct
            · obtain ⟨kk, hkk⟩ : ∃ kk, (r1B s read m).replicasWithMaxTag[sint.nat jv]? = some kk :=
                ⟨_, List.getElem?_eq_getElem (by simp only [sint.nat, sint.Z] at *; omega)⟩
              rw [r1_if_pos ⟨Hj0, Hif⟩]
              wp_apply wp_load_slice_index g3.replicasWithMaxTag' (sint.Z jv) _ (DFrac.own 1) kk Hj0
                $$ [Hrws] as Hrws
              · iframe Hrws; ipureintro; exact hkk
              wp_if_destruct
              · have hct := ct_hit _ _ _ (Hif ▸ hkk)
                wp_for_post
                try wp_auto
                wp_for_post
                iframe
                iexists iv + W32 1, rsl
                iframe
                rw [r2After_succ _ _ Hi.1 hc, if_pos hct, List.append_nil]
                iframe
                ipureintro; word
              · wp_for_post
                iframe
                iexists jv + W64 1
                iframe
                ipureintro
                have hj1 : sint.nat (jv + W64 1) = sint.nat jv + 1 := by
                  simp only [sint.nat, sint.Z] at *; word
                rw [hj1]
                refine ⟨by word, by simp only [sint.nat, sint.Z] at *; omega,
                  ct_step _ _ _ _ hkk Hif Hjc⟩
            · have hct : (r1B s read m).replicasWithMaxTag.contains iv = false :=
                ct_end _ _ _ (by simp only [sint.nat, sint.Z] at *; omega) Hjc
              try wp_auto
              wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.int32))))
                (Val (LiteralValueV _)))
              iapply wp_slice_literal (V := w32) (t := go.int32) [iv]
              wp_auto
              isplitl []
              · ipureintro; rfl
              iintro %sl_ptr ⟨Hsl, -⟩
              wp_apply wp_slice_append (V := w32) _ _ _ [iv] (DFrac.own 1) $$ [$Hrsl $Hrcap $Hsl]
                as %r2 ⟨Hr2, Hr2cap, -⟩
              wp_for_post
              iframe
              iexists iv + W32 1, r2
              iframe
              rw [r2After_succ _ _ Hi.1 hc, hct]
              iframe
              ipureintro; word
          have hi3 : iv = W32 3 := by word
          subst hi3
          rw [r2After_three]
          have hrepl : ([0, 1, 2] : List w32).filter
              (fun i => !((r1B s read m).replicasWithMaxTag.contains i)) =
              r2Reps (r1C (r1B s read m)) := by
            simp only [r2Reps, hC9]
          rw [hrepl]
          ihave %Hrl := ownSlice_len $$ Hrsl
          wp_apply HSt as %_ ⟨%st, %Hst', Hstats⟩
          subst Hst'
          wp_apply StatsMap.IncrementStrInt.wp' $$ [Hstats] as %_ -
          · stats_key
          · iframe Hstats
          have hl3 : (r2Reps (r1C (r1B s read m))).length ≤ 3 := by
            unfold r2Reps; exact Nat.le_trans (List.length_filter_le _ _) (by decide)
          have hlen : W64 3 - rsl.len = 3 - BitVec.ofNat 64 (r2Reps (r1C (r1B s read m))).length := by
            rw [Hrl.1]
            have h0 := Hrl.2
            simp only [sint.nat, sint.Z] at *
            word
          have hs2 : sendsTo (r2Reps (r1C (r1B s read m)))
              (.read2 (read2Msg k (r2Y (r1C (r1B s read m))) rv)) = some outs := by
            rw [← hsend, hid]; rfl
          ihave HS := HS2 $$ %p %(r2Y (r1C (r1B s read m))) %rv %rsl %_ %(r1S s read m).storeVT %outs %o
            %(And.intro hrv hs2)
          wp_apply HS $$ [HC Hp Hop Hrv Hrws Hrwc Hrsl] as %_ ⟨%_, HC, Hro, -⟩
          · iframe HC Hrsl
            iapply readOpRep_mk2 ρ p (r2Y (r1C (r1B s read m)))
              { g3 with numRead2Replies' := W64 3 - rsl.len } op w gd gm' read.clientId g.Op'
              g'.maxValTag' g3.ReadValTag' g3.replicasWithMaxTag'
              (r1C (r1B s read m)).readValTag (r1B s read m).replicasWithMaxTag
            · exact ⟨hOp3, by rw [G3, Hb2], rfl, rfl, by simp only [r2Y]; rw [hC2, hS2, hA2],
                rfl, by simp only [r2Y]; rw [hC9]⟩
            · exact ⟨by simp only [r2Y]; rw [hC4, hS4, HA1], by simp only [r2Y]; rw [hC1, hS1, hA1, Hrid],
                by simp only [r2Y]; rw [hC2, hS2, hA2, Hcid], Hkey, by simp only [r2Y]; rw [hC3, hS3, hA3, hN3],
                by simp only [r2Y]; rw [hC5, G4, hnr], hlen, by simp only [r2Y]; exact hrw3,
                by simp only [r2Y]; exact hsr3, by simp only [r2Y]; exact Hd3⟩
            iframe Hwr Hp Hdep Hop Hgm' Hrv Hrws Hrwc
          icases readOpRep_upd ρ p _ $$ Hro with ⟨%g4, Hp, Hcl⟩
          wp_auto
          ihave Hro := Hcl $$ Hp
          iapply HΦ
          isplitr [HC]
          · iapply coordOwn_close_r1 ρ co ic k s read m (r2Z (r1C (r1B s read m))) ropsR wopsR orR mtR
              fkR arS rm p hg Hrdom Hrk (by simp only [r2Z, r2Y]; rw [hC1, hC2]; exact hkey)
            iframe Hfix Hmisc Hw Ho Hrm Hrents Hro
          · rw [r1Put_storeVT]; iexact HC
        · rcases hcase with ⟨hq', -⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, hs', -⟩
          · rw [hq2] at hq'; cases hq'
          rotate_left
          · rw [hsent] at hs'; cases hs'
          try wp_auto
          iapply HΦ
          simp only [List.nil_append]
          isplitr [HC]
          · iapply coordOwn_close_r1 ρ co ic k s read m _ ropsR wopsR orR mtR fkR arS rm p hg Hrdom Hrk
              (by rw [hC1, hC2]; exact hkey)
            iframe Hfix Hmisc Hw Ho Hrm Hrents
            iapply readOpRep_mk ρ p _ g3 op w gd gm'
            · exact ⟨by rw [hC4, hS4, HA1], by rw [hC1, hS1, hA1, Hrid], by rw [hC2, hS2, hA2, Hcid], Hkey,
                by rw [hC3, hS3, hA3, hN3], by rw [hC5, G4, hnr], by rw [hC6, hS7, hA5, G5, Bg4, Ag4, H2],
                hrw3, by rw [← hsr3], Hd3⟩
            rw [hC2, hS2, hA2, hOp3, G3, Hb2, G8, hC9]
            iframe Hwr Hp Hdep Hop Hgm' Hrv Hrws Hrwc
          · rw [r1Put_storeVT]; iexact HC
    · have hq : model.sge (r1B s read m).numRead1Replies (model.NHALF + 1) = false := by
        simpa [model.sge, model.sle] using Hif
      rcases hcase with ⟨-, rfl, rfl⟩ | ⟨hq', -⟩
      rotate_left
      · rw [hq] at hq'; cases hq'
      iapply HΦ
      simp only [List.nil_append]
      isplitr [HC]
      · iapply coordOwn_close_r1 ρ co ic k s read m _ ropsR wopsR orR mtR fkR arS rm p hg Hrdom Hrk hkey
        iframe Hfix Hmisc Hw Ho Hrm Hrents
        iapply readOpRep_mk ρ p _ g'' op w gd gm'
        · exact ⟨by rw [hS4, HA1], by rw [hS1, hA1, Hrid], by rw [hS2, hA2, Hcid], Hkey,
            by rw [hS3, hA3, Bg2, Ag2, HN], hnr, by rw [hS7, hA5, Bg4, Ag4, H2],
            Hb1, by rw [hS8, hA6, Bg5, Ag5, H4], by rw [hS9, hA7, Bg6, Ag6, H5]⟩
        rw [hS2, hA2, Bg1, Ag1, Hb2, Bg3, Ag3, hS5, hA4]
        iframe Hwr Hp Hdep Hop Hgm' Hrv Hrws Hrwc
      · rw [r1Put_storeVT]; iexact HC

end

end Perennial.gryff.replica2

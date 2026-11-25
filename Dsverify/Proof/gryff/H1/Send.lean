/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/Send.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1e: the coordinator's send callbacks of `*gryff.Replica` (`SendRead1`, `SendRead2`,
`SendWrite1`, `SendWrite2`): each fills its scratch message (`scratchOwn`) and loops `send*To`
over the replicas (own id: a copy on its own channel with `pendingOuts_self`'s token; else
`SendMsg`).
-/
module

public import Dsverify.Proof.gryff.H1.HEnv
public import Dsverify.Proof.gryff.H1.PureParti
public import Dsverify.Proof.gryff.H1.PartiSpecs
public import Dsverify.Proof.gryff.H1.Iparti
public import Dsverify.Proof.gryff.N.Reply
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

/-- A send to replica `q` is to a replica id. -/
theorem sendTo_some (q : w32) (m : Msg) (o : Out) (hs : model.sendTo q m = some o) :
    ∃ d : Fin 3, o = .send d m ∧ q = rid32 d := by
  unfold model.sendTo model.dstOf at hs
  split at hs
  · rename_i hb
    simp only [Option.map_some, Option.some.injEq] at hs
    refine ⟨⟨(sint.Z q).toNat, by omega⟩, hs.symm, ?_⟩
    simp only [rid32]
    have : (((sint.Z q).toNat : Nat) : Int) = sint.Z q := by omega
    rw [this]; simp only [W32]; exact BitVec.ofInt_toInt.symm
  · cases hs

theorem rid32_inj (a b : Fin 3) (h : rid32 a = rid32 b) : a = b := by
  rcases a with ⟨_ | _ | _ | _, ha⟩ <;> rcases b with ⟨_ | _ | _ | _, hb⟩ <;>
    first | rfl | omega | (exfalso; simp [rid32] at h) | (exfalso; cases h)

/-- One step of `sendsTo`. -/
theorem sendsTo_cons (q : w32) (rs : List w32) (m : Msg) (outs : List Out)
    (h : sendsTo (q :: rs) m = some outs) :
    ∃ o rest, model.sendTo q m = some o ∧ sendsTo rs m = some rest ∧ outs = o :: rest := by
  unfold sendsTo at *
  simp only [List.mapM_cons] at h
  cases h1 : model.sendTo q m with
  | none => simp [h1] at h
  | some o =>
    cases h2 : rs.mapM (fun q => model.sendTo q m) with
    | none => simp [h1, h2] at h
    | some rest =>
      simp only [h1, h2] at h
      exact ⟨o, rest, rfl, rfl, (Option.some.inj h).symm⟩

theorem sendsTo_drop (rs : List w32) (m : Msg) (outs : List Out) (j : Nat) (hj : j < rs.length)
    (rem : List Out) (h : sendsTo (rs.drop j) m = some rem) :
    ∃ o rest, model.sendTo rs[j] m = some o ∧ sendsTo (rs.drop (j + 1)) m = some rest ∧
      rem = o :: rest := by
  rw [List.drop_eq_getElem_cons hj] at h
  exact sendsTo_cons _ _ m rem h

theorem sendsTo_nil (m : Msg) (rem : List Out) (h : sendsTo [] m = some rem) : rem = [] := by
  unfold sendsTo at h; simp at h; exact h

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

/-- `sendRead1To(q)`: the owed `Read1Proxied` (the scratch `r.read1`) goes to `q` (itself: a copy
on its channel). -/
theorem wp_sendRead1To (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (q : w32) (p : Loc) (mm : model.Read1ProxiedM) (o : Out)
    (outs : List Out) (ho : model.sendTo q (.read1 mm) = some o) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
        genericOk γ ρ k r gR h ∗ □ h1Fixed r gR ∗ r.[src.gryff.Replica, go!"read1"] ↦□ p ∗
        msgAt p (.read1 mm) ∗ pendingOuts γ ρ k r t (o :: outs) }}
      (App (repM r go!"sendRead1To") (Val #q))
    {{ RET #(); msgAt p (.read1 mm) ∗ pendingOuts γ ρ k r t outs }} := by
  obtain ⟨d, rfl, rfl⟩ := sendTo_some q _ o ho
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, #HgR, #HId, #Hgen, #Hfix, #Hp, Hm0, Hpend⟩ HΦ
  wp_method_call
  wp_call
  wp_auto
  wp_if_destruct
  · have hdk := rid32_inj d k Hif
    subst d
    icases (msgAt_read1 p _).1 $$ Hm0 with ⟨%g, Hg, %Hg⟩
    subst Hg
    wp_auto
    icases (isReplica_open ..).1 $$ Hrep with ⟨%gR1, %h1, Hex, #HgR1, -, -, -, -, -, -, Hch, -⟩
    icases (isExec_open ..).1 $$ Hex with ⟨%gR2, %mtx, %ex, %pp, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, #Hinv, -⟩
    unfold replicaChans
    icases Hch with ⟨Hb, -⟩
    unfold bagAt
    icases Hb with ⟨%ch, #Hchf, #Hbag⟩
    ihave Hm : msgAt read1Copy_ptr (.read1 (read1Of g)) $$ [read1Copy]
    · iapply (msgAt_read1 read1Copy_ptr _).2; iexists g; iframe; ipureintro; rfl
    ihave Hup := pendingOuts_self γ ρ k r t _ outs ⊤ (fun p hp => CoPset.subseteq_top p hp)
      $$ [$Hinv $Hpend]
    iapply fupd_wp
    imod Hup with ⟨%j, Hpend, Htok⟩
    imodintro
    wp_auto
    wp_apply (wp_bag_send (ρ.chans "read1") ch _ (msgChanP γ ρ k "read1")) $$
      [$Hbag Hm Htok]
    · unfold msgChanP
      iexists read1Copy_ptr, _
      iframe Hm
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      · iexists k, j; iexact Htok
    iapply HΦ; iframe
    iapply (msgAt_read1 p _).2; iexists g; iframe; ipureintro; rfl
  · have hdk : d ≠ k := fun e => Hif (by rw [e])
    unfold h1Fixed
    icases Hfix with ⟨%st, %cR1, %cR2, %cW1, %cW2, %cR1R, %cR2R, %cW1R, %cW2R, -, -, #Hc, #Hrc, -⟩
    ihave #Hpg : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr $$ []
    · iPkgInit
    have hsend := Replica.SendMsg.wp γ ρ k d r gR h t (.read1 mm) p cR1 outs hdk
    simp only [msgKind, msgTy] at hsend
    wp_auto
    wp_method_call
    wp_auto
    wp_apply hsend $$ [$Hpg $Hgen $HgR $Hrc $Hm0 $Hpend] as ⟨Hm, Hpend⟩
    iapply HΦ; iframe

/-- `sendRead2To(q)`: the owed `Read2Proxied` (the scratch `r.read2`) goes to `q` (itself: a copy
on its channel). -/
theorem wp_sendRead2To (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (q : w32) (p : Loc) (mm : model.Read2ProxiedM) (o : Out)
    (outs : List Out) (ho : model.sendTo q (.read2 mm) = some o) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
        genericOk γ ρ k r gR h ∗ □ h1Fixed r gR ∗ r.[src.gryff.Replica, go!"read2"] ↦□ p ∗
        msgAt p (.read2 mm) ∗ pendingOuts γ ρ k r t (o :: outs) }}
      (App (repM r go!"sendRead2To") (Val #q))
    {{ RET #(); msgAt p (.read2 mm) ∗ pendingOuts γ ρ k r t outs }} := by
  obtain ⟨d, rfl, rfl⟩ := sendTo_some q _ o ho
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, #HgR, #HId, #Hgen, #Hfix, #Hp, Hm0, Hpend⟩ HΦ
  wp_method_call
  wp_call
  wp_auto
  wp_if_destruct
  · have hdk := rid32_inj d k Hif
    subst d
    icases (msgAt_read2 p _).1 $$ Hm0 with ⟨%g, Hg, %Hg⟩
    subst Hg
    wp_auto
    icases (isReplica_open ..).1 $$ Hrep with ⟨%gR1, %h1, Hex, #HgR1, -, -, -, -, -, -, Hch, -⟩
    icases (isExec_open ..).1 $$ Hex with ⟨%gR2, %mtx, %ex, %pp, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, #Hinv, -⟩
    unfold replicaChans
    icases Hch with ⟨-, Hb, -⟩
    unfold bagAt
    icases Hb with ⟨%ch, #Hchf, #Hbag⟩
    ihave Hm : msgAt read2Copy_ptr (.read2 (read2Of g)) $$ [read2Copy]
    · iapply (msgAt_read2 read2Copy_ptr _).2; iexists g; iframe; ipureintro; rfl
    ihave Hup := pendingOuts_self γ ρ k r t _ outs ⊤ (fun p hp => CoPset.subseteq_top p hp)
      $$ [$Hinv $Hpend]
    iapply fupd_wp
    imod Hup with ⟨%j, Hpend, Htok⟩
    imodintro
    wp_auto
    wp_apply (wp_bag_send (ρ.chans "read2") ch _ (msgChanP γ ρ k "read2")) $$
      [$Hbag Hm Htok]
    · unfold msgChanP
      iexists read2Copy_ptr, _
      iframe Hm
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      · iexists k, j; iexact Htok
    iapply HΦ; iframe
    iapply (msgAt_read2 p _).2; iexists g; iframe; ipureintro; rfl
  · have hdk : d ≠ k := fun e => Hif (by rw [e])
    unfold h1Fixed
    icases Hfix with ⟨%st, %cR1, %cR2, %cW1, %cW2, %cR1R, %cR2R, %cW1R, %cW2R,
      -, -, -, -, #Hc, #Hrc, -⟩
    ihave #Hpg : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr $$ []
    · iPkgInit
    have hsend := Replica.SendMsg.wp γ ρ k d r gR h t (.read2 mm) p cR2 outs hdk
    simp only [msgKind, msgTy] at hsend
    wp_auto
    wp_method_call
    wp_auto
    wp_apply hsend $$ [$Hpg $Hgen $HgR $Hrc $Hm0 $Hpend] as ⟨Hm, Hpend⟩
    iapply HΦ; iframe

/-- `sendWrite1To(q)`: the owed `Write1Proxied` (the scratch `r.write1`) goes to `q` (itself: a copy
on its channel). -/
theorem wp_sendWrite1To (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (q : w32) (p : Loc) (mm : model.Write1ProxiedM) (o : Out)
    (outs : List Out) (ho : model.sendTo q (.write1 mm) = some o) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
        genericOk γ ρ k r gR h ∗ □ h1Fixed r gR ∗ r.[src.gryff.Replica, go!"write1"] ↦□ p ∗
        msgAt p (.write1 mm) ∗ pendingOuts γ ρ k r t (o :: outs) }}
      (App (repM r go!"sendWrite1To") (Val #q))
    {{ RET #(); msgAt p (.write1 mm) ∗ pendingOuts γ ρ k r t outs }} := by
  obtain ⟨d, rfl, rfl⟩ := sendTo_some q _ o ho
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, #HgR, #HId, #Hgen, #Hfix, #Hp, Hm0, Hpend⟩ HΦ
  wp_method_call
  wp_call
  wp_auto
  wp_if_destruct
  · have hdk := rid32_inj d k Hif
    subst d
    icases (msgAt_write1 p _).1 $$ Hm0 with ⟨%g, Hg, %Hg⟩
    subst Hg
    wp_auto
    icases (isReplica_open ..).1 $$ Hrep with ⟨%gR1, %h1, Hex, #HgR1, -, -, -, -, -, -, Hch, -⟩
    icases (isExec_open ..).1 $$ Hex with ⟨%gR2, %mtx, %ex, %pp, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, #Hinv, -⟩
    unfold replicaChans
    icases Hch with ⟨-, -, Hb, -⟩
    unfold bagAt
    icases Hb with ⟨%ch, #Hchf, #Hbag⟩
    ihave Hm : msgAt write1Copy_ptr (.write1 (write1Of g)) $$ [write1Copy]
    · iapply (msgAt_write1 write1Copy_ptr _).2; iexists g; iframe; ipureintro; rfl
    ihave Hup := pendingOuts_self γ ρ k r t _ outs ⊤ (fun p hp => CoPset.subseteq_top p hp)
      $$ [$Hinv $Hpend]
    iapply fupd_wp
    imod Hup with ⟨%j, Hpend, Htok⟩
    imodintro
    wp_auto
    wp_apply (wp_bag_send (ρ.chans "write1") ch _ (msgChanP γ ρ k "write1")) $$
      [$Hbag Hm Htok]
    · unfold msgChanP
      iexists write1Copy_ptr, _
      iframe Hm
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      · iexists k, j; iexact Htok
    iapply HΦ; iframe
    iapply (msgAt_write1 p _).2; iexists g; iframe; ipureintro; rfl
  · have hdk : d ≠ k := fun e => Hif (by rw [e])
    unfold h1Fixed
    icases Hfix with ⟨%st, %cR1, %cR2, %cW1, %cW2, %cR1R, %cR2R, %cW1R, %cW2R,
      -, -, -, -, -, -, #Hc, #Hrc, -⟩
    ihave #Hpg : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr $$ []
    · iPkgInit
    have hsend := Replica.SendMsg.wp γ ρ k d r gR h t (.write1 mm) p cW1 outs hdk
    simp only [msgKind, msgTy] at hsend
    wp_auto
    wp_method_call
    wp_auto
    wp_apply hsend $$ [$Hpg $Hgen $HgR $Hrc $Hm0 $Hpend] as ⟨Hm, Hpend⟩
    iapply HΦ; iframe

/-- `sendWrite2To(q)`: the owed `Write2Proxied` (the scratch `r.write2`) goes to `q` (itself: a copy
on its channel). -/
theorem wp_sendWrite2To (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (q : w32) (p : Loc) (mm : model.Write2ProxiedM) (o : Out)
    (outs : List Out) (ho : model.sendTo q (.write2 mm) = some o) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
        genericOk γ ρ k r gR h ∗ □ h1Fixed r gR ∗ r.[src.gryff.Replica, go!"write2"] ↦□ p ∗
        msgAt p (.write2 mm) ∗ pendingOuts γ ρ k r t (o :: outs) }}
      (App (repM r go!"sendWrite2To") (Val #q))
    {{ RET #(); msgAt p (.write2 mm) ∗ pendingOuts γ ρ k r t outs }} := by
  obtain ⟨d, rfl, rfl⟩ := sendTo_some q _ o ho
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, #HgR, #HId, #Hgen, #Hfix, #Hp, Hm0, Hpend⟩ HΦ
  wp_method_call
  wp_call
  wp_auto
  wp_if_destruct
  · have hdk := rid32_inj d k Hif
    subst d
    icases (msgAt_write2 p _).1 $$ Hm0 with ⟨%g, Hg, %Hg⟩
    subst Hg
    wp_auto
    icases (isReplica_open ..).1 $$ Hrep with ⟨%gR1, %h1, Hex, #HgR1, -, -, -, -, -, -, Hch, -⟩
    icases (isExec_open ..).1 $$ Hex with ⟨%gR2, %mtx, %ex, %pp, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, #Hinv, -⟩
    unfold replicaChans
    icases Hch with ⟨-, -, -, Hb, -⟩
    unfold bagAt
    icases Hb with ⟨%ch, #Hchf, #Hbag⟩
    ihave Hm : msgAt write2Copy_ptr (.write2 (write2Of g)) $$ [write2Copy]
    · iapply (msgAt_write2 write2Copy_ptr _).2; iexists g; iframe; ipureintro; rfl
    ihave Hup := pendingOuts_self γ ρ k r t _ outs ⊤ (fun p hp => CoPset.subseteq_top p hp)
      $$ [$Hinv $Hpend]
    iapply fupd_wp
    imod Hup with ⟨%j, Hpend, Htok⟩
    imodintro
    wp_auto
    wp_apply (wp_bag_send (ρ.chans "write2") ch _ (msgChanP γ ρ k "write2")) $$
      [$Hbag Hm Htok]
    · unfold msgChanP
      iexists write2Copy_ptr, _
      iframe Hm
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      · iexists k, j; iexact Htok
    iapply HΦ; iframe
    iapply (msgAt_write2 p _).2; iexists g; iframe; ipureintro; rfl
  · have hdk : d ≠ k := fun e => Hif (by rw [e])
    unfold h1Fixed
    icases Hfix with ⟨%st, %cR1, %cR2, %cW1, %cW2, %cR1R, %cR2R, %cW1R, %cW2R,
      -, -, -, -, -, -, -, -, #Hc, #Hrc, -⟩
    ihave #Hpg : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr $$ []
    · iPkgInit
    have hsend := Replica.SendMsg.wp γ ρ k d r gR h t (.write2 mm) p cW2 outs hdk
    simp only [msgKind, msgTy] at hsend
    wp_auto
    wp_method_call
    wp_auto
    wp_apply hsend $$ [$Hpg $Hgen $HgR $Hrc $Hm0 $Hpend] as ⟨Hm, Hpend⟩
    iapply HΦ; iframe

variable [pD : GryffPartiDeps (GF := GF)] in
/-- **`SendRead1(rop, replicas)`** on `coordCtx`. -/
theorem wp_Replica_SendRead1 (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r pa : Loc)
    (t : List Ev) (ong : AMap 32 w32) (rop : Loc) (ro : ReadOp) (sl : GoSlice) (rs : List w32)
    (vt : model.ValTag) (outs o : List Out)
    (hs : sendsTo rs (.read1 (read1Msg k ro vt)) = some outs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"parti"] ↦□ pa ∗
        coordCtx γ ρ k r pa t ong vt (outs ++ o) ∗ readOpRep ρ rop ro ∗ sl ↦* rs }}
      (App (App (repM r go!"SendRead1") (Val #rop)) (Val #sl))
    {{ RET #(); coordCtx γ ρ k r pa t ong vt o ∗ readOpRep ρ rop ro ∗ sl ↦* rs }} := by
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, #Hpa, HC, Hrop, Hsl⟩ HΦ
  icases (isReplica_open ..).1 $$ Hrep with ⟨%gR0, %h, -, #HgR0, -, -, -, -, -, -, -, #Hgen⟩
  ihave #Hfix := genericOk_h1Fixed γ ρ k r gR0 h $$ Hgen
  icases genericOk_send γ ρ k r gR0 h $$ Hgen with ⟨#HId, -⟩
  unfold coordCtx
  icases HC with ⟨%gR, #HgR, Hpo, HV, Hsc, Hpend⟩
  icombine HgR HgR0 gives %HeqR
  subst HeqR
  unfold scratchOwn
  icases Hsc with ⟨%p1, %p2, %p3, %p4, %v1, %v2, %v3, %v4, #Hp1, Hv1, #Hp2, Hv2, #Hp3, Hv3,
    #Hp4, Hv4, %HD⟩
  unfold readOpRep
  icases Hrop with ⟨%g, %op, %rws, %w, %gd, #Hw, Hg, #Hdep, Hop, Hmv, Hrv, Hrws, Hcap, %Hgo⟩
  ihave #Hpc : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon $$ []
  · iPkgInit
  obtain ⟨hrid, hcid, hkey, Hgo'⟩ := Hgo
  wp_method_call
  wp_call
  wp_auto
  rw [hkey]
  wp_apply (GryffPartiDeps.getStoreMetadata (GF := GF) (hG := hG) _ _ _ _ _) $$ [$Hpc $Hpo] as %md ⟨%tp, %gt, %Htag, #Htp, Hmd, Hback⟩
  try wp_auto
  wp_apply wp_Replica_GetCurrentValue $$ [$Hpkg $HgR $HV] as HV
  dsimp only
  ihave Hpo := Hback $$ Hmd
  ihave #Hdl : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
  · iPkgInit
  ihave #Hdlog := replica.dlog_init_access $$ Hdl
  wp_lit_drop
  wp_auto
  wp_apply wp_Replica_Printf $$ [$Hdlog]
  -- the message sent
  have hD : depOf v1.D' = model.dep0 := HD -- H1e-1 (`scratchOwn` keeps `D` zero)
  have hmm : read1Of (⟨op.RequestId', op.ClientId', W64 0, v1.D', rid32 k, ⟨vt.v, gt⟩⟩ :
      src.gryffproto.Read1Proxied) = read1Msg k ro vt := by
    simp only [read1Of, read1Msg, vtOf, hrid, hcid, hD, Htag]; rfl
  ihave Hm : msgAt p1 (.read1 (read1Msg k ro vt)) $$ [Hv1]
  · iapply (msgAt_read1 p1 _).2; iexists _; iframe; ipureintro; exact hmm
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave HI : (∃ j : Nat, "i" ∷ i_ptr ↦ W64 (j : Int) ∗ "%Hj" ∷ ⌜j ≤ rs.length⌝ ∗ "Hsl" ∷ sl ↦* rs ∗
      "Hm" ∷ msgAt p1 (.read1 (read1Msg k ro vt)) ∗
      ∃ rem : List Out, "%Hrem" ∷ ⌜sendsTo (rs.drop j) (.read1 (read1Msg k ro vt)) = some rem⌝ ∗
        "Hpend" ∷ pendingOuts γ ρ k r t (rem ++ o) : IProp GF) $$ [i Hsl Hm Hpend]
  · iexists 0
    iframe i Hsl Hm
    isplitr
    · ipureintro; omega
    iexists outs
    iframe Hpend
    ipureintro; simpa using hs
  wp_for HI
  icases HI with ⟨%rem, %Hrem, Hpend⟩
  have hjz : sint.Z (W64 (j : Int)) = j := by
    have := Hlen.1; simp only [sint.nat, sint.Z] at *; word
  rw [hjz]
  wp_if_destruct
  · have hjl : j < rs.length := by
      have := Hlen.1; simp only [sint.nat, sint.Z] at *; omega
    obtain ⟨o1, rest, hso, hrest, rfl⟩ := sendsTo_drop rs _ outs j hjl rem Hrem
    rw [if_pos' ⟨by rw [hjz]; omega, by rw [hjz]; exact Hif⟩, hjz]
    wp_apply wp_load_slice_index sl (j : Int) rs (DFrac.own 1) rs[j] (by omega) $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; simp [hjl]
    rw [List.cons_append]
    wp_apply (wp_sendRead1To γ ρ k r gR h t rs[j] p1 (read1Msg k ro vt) o1 (rest ++ o) hso) $$
      [$Hpkg $Hrep $HgR0 $HId $Hgen $Hfix $Hp1 $Hm $Hpend] as ⟨Hm, Hpend⟩
    wp_for_post
    iframe
    iexists (j + 1)
    iframe Hsl Hm
    isplitl [i]
    · rw [show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]; iexact i
    isplitr
    · ipureintro; omega
    iexists rest
    iframe Hpend
    ipureintro; exact hrest
  · have hjl : j = rs.length := by
      have := Hlen.1; simp only [sint.nat, sint.Z] at *; omega
    subst hjl
    rw [List.drop_length] at Hrem
    have := sendsTo_nil _ rem Hrem
    subst this
    rw [List.nil_append]
    icases (msgAt_read1 p1 _).1 $$ Hm with ⟨%g1, Hv1, %Hg1⟩
    have HD1 : depOf g1.D' = model.dep0 := by
      have := congrArg model.Read1ProxiedM.d Hg1
      simpa only [read1Of, read1Msg] using this
    iapply HΦ
    iframe Hsl
    isplitl [HV Hpo Hv1 Hv2 Hv3 Hv4 Hpend]
    · iexists gR
      iframe HgR HV Hpo Hpend
      iexists p1, p2, p3, p4, g1, v2, v3, v4
      iframe # ∗
      try (ipureintro; exact HD1)
    · iexists g, op, rws, w, gd
      iframe # ∗
      ipureintro; exact ⟨hrid, hcid, hkey, Hgo'⟩
  done

/-- **`SendRead2(rop, replicas)`** on `coordCtx`. -/
theorem wp_Replica_SendRead2 (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r pa : Loc)
    (t : List Ev) (ong : AMap 32 w32) (rop : Loc) (ro : ReadOp) (rv : model.ValTag) (sl : GoSlice)
    (rs : List w32) (vt : model.ValTag) (outs o : List Out) (hrv : ro.readValTag = some rv)
    (hs : sendsTo rs (.read2 (read2Msg k ro rv)) = some outs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        coordCtx γ ρ k r pa t ong vt (outs ++ o) ∗ readOpRep ρ rop ro ∗ sl ↦* rs }}
      (App (App (repM r go!"SendRead2") (Val #rop)) (Val #sl))
    {{ RET #(); coordCtx γ ρ k r pa t ong vt o ∗ readOpRep ρ rop ro ∗ sl ↦* rs }} := by
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, HC, Hrop, Hsl⟩ HΦ
  icases (isReplica_open ..).1 $$ Hrep with ⟨%gR0, %h, -, #HgR0, -, -, -, -, -, -, -, #Hgen⟩
  ihave #Hfix := genericOk_h1Fixed γ ρ k r gR0 h $$ Hgen
  icases genericOk_send γ ρ k r gR0 h $$ Hgen with ⟨#HId, -⟩
  unfold coordCtx
  icases HC with ⟨%gR, #HgR, Hpo, HV, Hsc, Hpend⟩
  icombine HgR HgR0 gives %HeqR
  subst HeqR
  unfold scratchOwn
  icases Hsc with ⟨%p1, %p2, %p3, %p4, %v1, %v2, %v3, %v4, #Hp1, Hv1, #Hp2, Hv2, #Hp3, Hv3,
    #Hp4, Hv4, %HD⟩
  unfold readOpRep
  rw [hrv]
  icases Hrop with ⟨%g, %op, %rws, %w, %gd, #Hw, Hg, #Hdep, Hop, Hmv, Hrv, Hrws, Hcap, %Hgo⟩
  simp only [optVtRep]
  icases Hrv with ⟨%grv, #Hgrv, %Hgrv⟩
  obtain ⟨hrid, hcid, hkey, Hgo'⟩ := Hgo
  wp_method_call
  wp_call
  wp_auto
  dsimp only
  ihave Hm : msgAt p2 (.read2 (read2Msg k ro rv)) $$ [Hv2]
  · iapply (msgAt_read2 p2 _).2; iexists _; iframe
    ipureintro; simp only [read2Of, read2Msg, hrid, hcid, hkey, Hgrv]; rfl
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave HI : (∃ j : Nat, "i" ∷ i_ptr ↦ W64 (j : Int) ∗ "%Hj" ∷ ⌜j ≤ rs.length⌝ ∗ "Hsl" ∷ sl ↦* rs ∗
      "Hm" ∷ msgAt p2 (.read2 (read2Msg k ro rv)) ∗
      ∃ rem : List Out, "%Hrem" ∷ ⌜sendsTo (rs.drop j) (.read2 (read2Msg k ro rv)) = some rem⌝ ∗
        "Hpend" ∷ pendingOuts γ ρ k r t (rem ++ o) : IProp GF) $$ [i Hsl Hm Hpend]
  · iexists 0
    iframe i Hsl Hm
    isplitr
    · ipureintro; omega
    iexists outs
    iframe Hpend
    ipureintro; simpa using hs
  wp_for HI
  icases HI with ⟨%rem, %Hrem, Hpend⟩
  have hjz : sint.Z (W64 (j : Int)) = j := by
    have := Hlen.1; simp only [sint.nat, sint.Z] at *; word
  rw [hjz]
  wp_if_destruct
  · have hjl : j < rs.length := by
      have := Hlen.1; simp only [sint.nat, sint.Z] at *; omega
    obtain ⟨o1, rest, hso, hrest, rfl⟩ := sendsTo_drop rs _ outs j hjl rem Hrem
    rw [if_pos' ⟨by rw [hjz]; omega, by rw [hjz]; exact Hif⟩, hjz]
    wp_apply wp_load_slice_index sl (j : Int) rs (DFrac.own 1) rs[j] (by omega) $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; simp [hjl]
    rw [List.cons_append]
    wp_apply (wp_sendRead2To γ ρ k r gR h t rs[j] p2 (read2Msg k ro rv) o1 (rest ++ o) hso) $$
      [$Hpkg $Hrep $HgR0 $HId $Hgen $Hfix $Hp2 $Hm $Hpend] as ⟨Hm, Hpend⟩
    wp_for_post
    iframe
    iexists (j + 1)
    iframe Hsl Hm
    isplitl [i]
    · rw [show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]; iexact i
    isplitr
    · ipureintro; omega
    iexists rest
    iframe Hpend
    ipureintro; exact hrest
  · have hjl : j = rs.length := by
      have := Hlen.1; simp only [sint.nat, sint.Z] at *; omega
    subst hjl
    rw [List.drop_length] at Hrem
    have := sendsTo_nil _ rem Hrem
    subst this
    rw [List.nil_append]
    icases (msgAt_read2 p2 _).1 $$ Hm with ⟨%g1, Hv2, -⟩
    iapply HΦ
    iframe Hsl
    isplitl [HV Hpo Hv1 Hv2 Hv3 Hv4 Hpend]
    · iexists gR
      iframe HgR HV Hpo Hpend
      iexists p1, p2, p3, p4, v1, g1, v3, v4
      iframe # ∗
      try (ipureintro; exact HD)
    · iexists g, op, rws, w, gd
      iframe # ∗
      ipureintro; exact ⟨Hgrv, hrid, hcid, hkey, Hgo'⟩

/-- `*wop.MaxAppliedTag` (`SendWrite1`): the coordinator's `maxAppliedTag` or a persistent tag. -/
theorem wp_load_maxAppliedTag (l co : Loc) (mat : src.gryffproto.Tag) :
    {{ ((⌜l = co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"]⌝ ∨
          ∃ gt : src.gryffproto.Tag, l ↦□ gt) : IProp GF) ∗
        co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"] ↦ mat }}
      (App (Val (GoInstruction (GoLoad src.gryffproto.Tag.ty))) (Val #l))
    {{ (x : src.gryffproto.Tag), RET #x;
        ((⌜l = co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"]⌝ ∨
          ∃ gt : src.gryffproto.Tag, l ↦□ gt) : IProp GF) ∗
        co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"] ↦ mat }} := by
  wp_start as ⟨Hd, Hco⟩
  icases Hd with (%He | ⟨%gt, #Hgt⟩)
  · subst He
    wp_apply (IntoValTyped.wp_load (t := src.gryffproto.Tag.ty) _ _ _) $$ Hco as Hco
    iapply HΦ
    iframe Hco
    ileft; ipureintro; rfl
  · wp_apply (IntoValTyped.wp_load (t := src.gryffproto.Tag.ty) _ _ _) $$ Hgt as -
    iapply HΦ
    iframe Hco
    iright; iexists gt; iexact Hgt

set_option maxHeartbeats 1600000 in
/-- **`SendWrite1(wop, replicas)`** on `coordCtx`. -/
theorem wp_Replica_SendWrite1 (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r pa : Loc)
    (t : List Ev) (ong : AMap 32 w32) (co wop : Loc) (wo : WriteOp) (mat : src.gryffproto.Tag)
    (sl : GoSlice) (rs : List w32) (vt : model.ValTag) (outs o : List Out)
    (hs : sendsTo rs (.write1 (write1Msg k wo)) = some outs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        coordCtx γ ρ k r pa t ong vt (outs ++ o) ∗ writeOpRep ρ co wop wo ∗
        co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"] ↦ mat ∗ sl ↦*□ rs }}
      (App (App (repM r go!"SendWrite1") (Val #wop)) (Val #sl))
    {{ RET #(); coordCtx γ ρ k r pa t ong vt o ∗ writeOpRep ρ co wop wo ∗
        co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"] ↦ mat }} := by
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, HC, Hwop, Hco, #Hsl⟩ HΦ
  icases (isReplica_open ..).1 $$ Hrep with ⟨%gR0, %h, -, #HgR0, -, -, -, -, -, -, -, #Hgen⟩
  ihave #Hfix := genericOk_h1Fixed γ ρ k r gR0 h $$ Hgen
  icases genericOk_send γ ρ k r gR0 h $$ Hgen with ⟨#HId, -⟩
  unfold coordCtx
  icases HC with ⟨%gR, #HgR, Hpo, HV, Hsc, Hpend⟩
  icombine HgR HgR0 gives %HeqR
  subst HeqR
  unfold scratchOwn
  icases Hsc with ⟨%p1, %p2, %p3, %p4, %v1, %v2, %v3, %v4, #Hp1, Hv1, #Hp2, Hv2, #Hp3, Hv3,
    #Hp4, Hv4, %HD⟩
  unfold writeOpRep
  icases Hwop with ⟨%g, %op, %wr, %gd, #Hw, Hg, Hop, #Hdep, Hmat, Hmv, Hwt, %Hgo⟩
  obtain ⟨hrid, hcid, hkey, hn, hdep, hwv, hfw, Hgo'⟩ := Hgo
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_load_maxAppliedTag $$ [$Hmat $Hco] as %mx ⟨Hmat, Hco⟩
  try wp_auto
  dsimp only
  ihave Hm : msgAt p3 (.write1 (write1Msg k wo)) $$ [Hv3]
  · iapply (msgAt_write1 p3 _).2; iexists _; iframe
    ipureintro; simp only [write1Of, write1Msg, hrid, hcid, hkey, hfw, hdep]; rfl
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave HI : (∃ j : Nat, "i" ∷ i_ptr ↦ W64 (j : Int) ∗ "%Hj" ∷ ⌜j ≤ rs.length⌝ ∗
      "Hm" ∷ msgAt p3 (.write1 (write1Msg k wo)) ∗
      ∃ rem : List Out, "%Hrem" ∷ ⌜sendsTo (rs.drop j) (.write1 (write1Msg k wo)) = some rem⌝ ∗
        "Hpend" ∷ pendingOuts γ ρ k r t (rem ++ o) : IProp GF) $$ [i Hsl Hm Hpend]
  · iexists 0
    iframe i Hm
    isplitr
    · ipureintro; omega
    iexists outs
    iframe Hpend
    ipureintro; simpa using hs
  wp_for HI
  icases HI with ⟨%rem, %Hrem, Hpend⟩
  have hjz : sint.Z (W64 (j : Int)) = j := by
    have := Hlen.1; simp only [sint.nat, sint.Z] at *; word
  rw [hjz]
  wp_if_destruct
  · have hjl : j < rs.length := by
      have := Hlen.1; simp only [sint.nat, sint.Z] at *; omega
    obtain ⟨o1, rest, hso, hrest, rfl⟩ := sendsTo_drop rs _ outs j hjl rem Hrem
    rw [if_pos' ⟨by rw [hjz]; omega, by rw [hjz]; exact Hif⟩, hjz]
    wp_apply wp_load_slice_index sl (j : Int) rs DFrac.discard rs[j] (by omega) $$ [Hsl] as -
    · iframe Hsl; ipureintro; simp [hjl]
    rw [List.cons_append]
    wp_apply (wp_sendWrite1To γ ρ k r gR h t rs[j] p3 (write1Msg k wo) o1 (rest ++ o) hso) $$
      [$Hpkg $Hrep $HgR0 $HId $Hgen $Hfix $Hp3 $Hm $Hpend] as ⟨Hm, Hpend⟩
    wp_for_post
    iframe
    iexists (j + 1)
    iframe Hm
    isplitl [i]
    · rw [show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]; iexact i
    isplitr
    · ipureintro; omega
    iexists rest
    iframe Hpend
    ipureintro; exact hrest
  · have hjl : j = rs.length := by
      have := Hlen.1; simp only [sint.nat, sint.Z] at *; omega
    subst hjl
    rw [List.drop_length] at Hrem
    have := sendsTo_nil _ rem Hrem
    subst this
    rw [List.nil_append]
    icases (msgAt_write1 p3 _).1 $$ Hm with ⟨%g1, Hv3, -⟩
    iapply HΦ
    iframe Hco
    isplitl [HV Hpo Hv1 Hv2 Hv3 Hv4 Hpend]
    · iexists gR
      iframe HgR HV Hpo Hpend
      iexists p1, p2, p3, p4, v1, v2, g1, v4
      iframe # ∗
      try (ipureintro; exact HD)
    · iexists g, op, wr, gd
      iframe # ∗
      ipureintro; exact ⟨hrid, hcid, hkey, hn, hdep, hwv, hfw, Hgo'⟩

set_option maxHeartbeats 1600000 in
/-- **`SendWrite2(wop, replicas)`** on `coordCtx`. -/
theorem wp_Replica_SendWrite2 (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r pa : Loc)
    (t : List Ev) (ong : AMap 32 w32) (co wop : Loc) (wo : WriteOp) (wt : model.Tag)
    (sl : GoSlice) (rs : List w32) (vt : model.ValTag) (outs o : List Out)
    (hwt : wo.writeTag = some wt)
    (hs : sendsTo rs (.write2 (write2Msg k wo wt)) = some outs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        coordCtx γ ρ k r pa t ong vt (outs ++ o) ∗ writeOpRep ρ co wop wo ∗ sl ↦*□ rs }}
      (App (App (repM r go!"SendWrite2") (Val #wop)) (Val #sl))
    {{ RET #(); coordCtx γ ρ k r pa t ong vt o ∗ writeOpRep ρ co wop wo }} := by
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, HC, Hwop, #Hsl⟩ HΦ
  icases (isReplica_open ..).1 $$ Hrep with ⟨%gR0, %h, -, #HgR0, -, -, -, -, -, -, -, #Hgen⟩
  ihave #Hfix := genericOk_h1Fixed γ ρ k r gR0 h $$ Hgen
  icases genericOk_send γ ρ k r gR0 h $$ Hgen with ⟨#HId, -⟩
  unfold coordCtx
  icases HC with ⟨%gR, #HgR, Hpo, HV, Hsc, Hpend⟩
  icombine HgR HgR0 gives %HeqR
  subst HeqR
  unfold scratchOwn
  icases Hsc with ⟨%p1, %p2, %p3, %p4, %v1, %v2, %v3, %v4, #Hp1, Hv1, #Hp2, Hv2, #Hp3, Hv3,
    #Hp4, Hv4, %HD⟩
  unfold writeOpRep
  rw [hwt]
  icases Hwop with ⟨%g, %op, %wr, %gd, #Hw, Hg, Hop, #Hdep, Hmat, Hmv, Hwt, %Hgo⟩
  icases Hwt with ⟨%gt, #Hgt, %Htag⟩
  obtain ⟨hrid, hcid, hkey, hn, hdep, hwv, hfw, Hgo'⟩ := Hgo
  wp_method_call
  wp_call
  wp_auto
  dsimp only
  ihave Hm : msgAt p4 (.write2 (write2Msg k wo wt)) $$ [Hv4]
  · iapply (msgAt_write2 p4 _).2; iexists _; iframe
    ipureintro; simp only [write2Of, write2Msg, vtOf, hrid, hcid, hkey, hwv, Htag]; rfl
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave HI : (∃ j : Nat, "i" ∷ i_ptr ↦ W64 (j : Int) ∗ "%Hj" ∷ ⌜j ≤ rs.length⌝ ∗
      "Hm" ∷ msgAt p4 (.write2 (write2Msg k wo wt)) ∗
      ∃ rem : List Out, "%Hrem" ∷ ⌜sendsTo (rs.drop j) (.write2 (write2Msg k wo wt)) = some rem⌝ ∗
        "Hpend" ∷ pendingOuts γ ρ k r t (rem ++ o) : IProp GF) $$ [i Hsl Hm Hpend]
  · iexists 0
    iframe i Hm
    isplitr
    · ipureintro; omega
    iexists outs
    iframe Hpend
    ipureintro; simpa using hs
  wp_for HI
  icases HI with ⟨%rem, %Hrem, Hpend⟩
  have hjz : sint.Z (W64 (j : Int)) = j := by
    have := Hlen.1; simp only [sint.nat, sint.Z] at *; word
  rw [hjz]
  wp_if_destruct
  · have hjl : j < rs.length := by
      have := Hlen.1; simp only [sint.nat, sint.Z] at *; omega
    obtain ⟨o1, rest, hso, hrest, rfl⟩ := sendsTo_drop rs _ outs j hjl rem Hrem
    rw [if_pos' ⟨by rw [hjz]; omega, by rw [hjz]; exact Hif⟩, hjz]
    wp_apply wp_load_slice_index sl (j : Int) rs DFrac.discard rs[j] (by omega) $$ [Hsl] as -
    · iframe Hsl; ipureintro; simp [hjl]
    rw [List.cons_append]
    wp_apply (wp_sendWrite2To γ ρ k r gR h t rs[j] p4 (write2Msg k wo wt) o1 (rest ++ o) hso) $$
      [$Hpkg $Hrep $HgR0 $HId $Hgen $Hfix $Hp4 $Hm $Hpend] as ⟨Hm, Hpend⟩
    wp_for_post
    iframe
    iexists (j + 1)
    iframe Hm
    isplitl [i]
    · rw [show W64 ((j + 1 : Nat) : Int) = W64 (j : Int) + W64 1 by word]; iexact i
    isplitr
    · ipureintro; omega
    iexists rest
    iframe Hpend
    ipureintro; exact hrest
  · have hjl : j = rs.length := by
      have := Hlen.1; simp only [sint.nat, sint.Z] at *; omega
    subst hjl
    rw [List.drop_length] at Hrem
    have := sendsTo_nil _ rem Hrem
    subst this
    rw [List.nil_append]
    icases (msgAt_write2 p4 _).1 $$ Hm with ⟨%g1, Hv4, -⟩
    iapply HΦ
    isplitl [HV Hpo Hv1 Hv2 Hv3 Hv4 Hpend]
    · iexists gR
      iframe HgR HV Hpo Hpend
      iexists p1, p2, p3, p4, v1, v2, v3, g1
      iframe # ∗
      try (ipureintro; exact HD)
    · iexists g, op, wr, gd
      iframe # ∗
      ipureintro; exact ⟨Htag, hrid, hcid, hkey, hn, hdep, hwv, hfw, Hgo'⟩

end

end Perennial.gryff.replica2

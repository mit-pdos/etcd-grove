/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H1/GParti.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H1d: the gryff handlers of the participant's events (`handleRead1Proxied`,
`handleRead2Proxied`, `handleWrite1Proxied`, `handleWrite2Proxied`): the participant's method
specs, `Replica_ipartiOk` (H1b's `Replica_ipartiOk_proof`), the `reply*Replica` sends (own channel
with `pendingOuts_self`'s token, or `SendMsg`) and the frame lemmas (`ppf`).
-/
module

public import Dsverify.Proof.gryff.H1.HEnv
public import Dsverify.Proof.gryff.H1.Icoord
public import Dsverify.Proof.gryff.H1.PureParti
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Replica2.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal ReadOp WriteOp OngoingOp
  Msg Ev Ext Out Cmd Deps AMap StepRes)
open Perennial.gryff.replica (XS)

attribute [local instance] GooseGlobalGS.gooseInvGS

-- `sendTo_some`, `rid32_inj`: moved to `H1/Send.lean` (unit H1e imports them without `GParti`).

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

/-- `replyRead1Replica(q, rp)`: the owed reply goes to `q` (itself: its channel). -/
theorem wp_replyRead1Replica (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (q : w32) (rp : Loc) (g : src.gryffproto.Read1Reply) (o : Out)
    (outs : List Out) (ho : model.sendTo q (.read1Reply (read1ReplyOf g)) = some o) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
        genericOk γ ρ k r gR h ∗ □ h1Fixed r gR ∗ rp ↦ g ∗ pendingOuts γ ρ k r t (o :: outs) }}
      (App (App (repM r go!"replyRead1Replica") (Val #q)) (Val #rp))
    {{ RET #(); pendingOuts γ ρ k r t outs }} := by
  obtain ⟨d, rfl, rfl⟩ := sendTo_some q _ o ho
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, #HgR, #HId, #Hgen, #Hfix, Hrp, Hpend⟩ HΦ
  ihave Hm : msgAt rp (.read1Reply (read1ReplyOf g)) $$ [Hrp]
  · iapply (msgAt_read1Reply rp _).2; iexists g; iframe; ipureintro; rfl
  wp_method_call
  wp_call
  wp_auto
  wp_if_destruct
  · have hdk := rid32_inj d k Hif
    subst d
    icases (isReplica_open ..).1 $$ Hrep with ⟨%gR1, %h1, Hex, #HgR1, -, -, -, -, -, -, Hch, -⟩
    icases (isExec_open ..).1 $$ Hex with ⟨%gR2, %mtx, %ex, %pp, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, #Hinv, -⟩ -- H-X-4: one more slot (Shutdown)
    unfold replicaChans
    icases Hch with ⟨-, -, -, -, Hb, -⟩
    unfold bagAt
    icases Hb with ⟨%ch, #Hchf, #Hbag⟩
    ihave Hup := pendingOuts_self γ ρ k r t _ outs ⊤ (fun p hp => CoPset.subseteq_top p hp)
      $$ [$Hinv $Hpend]
    iapply fupd_wp
    imod Hup with ⟨%j, Hpend, Htok⟩
    imodintro
    wp_auto
    wp_apply (wp_bag_send (ρ.chans "read1Reply") ch _ (msgChanP γ ρ k "read1Reply")) $$
      [$Hbag Hm Htok]
    · unfold msgChanP
      iexists rp, _
      iframe Hm
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      · iexists k, j; iexact Htok
    iapply HΦ; iexact Hpend
  · have hdk : d ≠ k := fun e => Hif (by rw [e])
    unfold h1Fixed
    icases Hfix with ⟨%st, %cR1, %cR2, %cW1, %cW2, %cR1R, %cR2R, %cW1R, %cW2R, -, -, -, -, -, -,
      -, -, -, -, #Hc, #Hrc, -⟩
    ihave #Hpg : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr $$ []
    · iPkgInit
    have hsend := Replica.SendMsg.wp γ ρ k d r gR h t (.read1Reply (read1ReplyOf g)) rp cR1R
      outs hdk
    simp only [msgKind, msgTy] at hsend
    wp_auto
    wp_method_call
    wp_auto
    wp_apply hsend $$ [$Hpg $Hgen $HgR $Hrc $Hm $Hpend] as ⟨-, Hpend⟩
    iapply HΦ; iexact Hpend

/-- `replyRead2Replica(q, rp)`: the owed reply goes to `q` (itself: its channel). -/
theorem wp_replyRead2Replica (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (q : w32) (rp : Loc) (g : src.gryffproto.Read2Reply) (o : Out)
    (outs : List Out) (ho : model.sendTo q (.read2Reply (read2ReplyOf g)) = some o) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
        genericOk γ ρ k r gR h ∗ □ h1Fixed r gR ∗ rp ↦ g ∗ pendingOuts γ ρ k r t (o :: outs) }}
      (App (App (repM r go!"replyRead2Replica") (Val #q)) (Val #rp))
    {{ RET #(); pendingOuts γ ρ k r t outs }} := by
  obtain ⟨d, rfl, rfl⟩ := sendTo_some q _ o ho
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, #HgR, #HId, #Hgen, #Hfix, Hrp, Hpend⟩ HΦ
  ihave Hm : msgAt rp (.read2Reply (read2ReplyOf g)) $$ [Hrp]
  · iapply (msgAt_read2Reply rp _).2; iexists g; iframe; ipureintro; rfl
  wp_method_call
  wp_call
  wp_auto
  wp_if_destruct
  · have hdk := rid32_inj d k Hif
    subst d
    icases (isReplica_open ..).1 $$ Hrep with ⟨%gR1, %h1, Hex, #HgR1, -, -, -, -, -, -, Hch, -⟩
    icases (isExec_open ..).1 $$ Hex with ⟨%gR2, %mtx, %ex, %pp, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, #Hinv, -⟩ -- H-X-4: one more slot (Shutdown)
    unfold replicaChans
    icases Hch with ⟨-, -, -, -, -, Hb, -⟩
    unfold bagAt
    icases Hb with ⟨%ch, #Hchf, #Hbag⟩
    ihave Hup := pendingOuts_self γ ρ k r t _ outs ⊤ (fun p hp => CoPset.subseteq_top p hp)
      $$ [$Hinv $Hpend]
    iapply fupd_wp
    imod Hup with ⟨%j, Hpend, Htok⟩
    imodintro
    wp_auto
    wp_apply (wp_bag_send (ρ.chans "read2Reply") ch _ (msgChanP γ ρ k "read2Reply")) $$
      [$Hbag Hm Htok]
    · unfold msgChanP
      iexists rp, _
      iframe Hm
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      · iexists k, j; iexact Htok
    iapply HΦ; iexact Hpend
  · have hdk : d ≠ k := fun e => Hif (by rw [e])
    unfold h1Fixed
    icases Hfix with ⟨%st, %cR1, %cR2, %cW1, %cW2, %cR1R, %cR2R, %cW1R, %cW2R, -, -, -, -, -, -,
      -, -, -, -, -, -, #Hc, #Hrc, -⟩
    ihave #Hpg : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr $$ []
    · iPkgInit
    have hsend := Replica.SendMsg.wp γ ρ k d r gR h t (.read2Reply (read2ReplyOf g)) rp cR2R
      outs hdk
    simp only [msgKind, msgTy] at hsend
    wp_auto
    wp_method_call
    wp_auto
    wp_apply hsend $$ [$Hpg $Hgen $HgR $Hrc $Hm $Hpend] as ⟨-, Hpend⟩
    iapply HΦ; iexact Hpend

/-- `replyWrite1Replica(q, rp)`: the owed reply goes to `q` (itself: its channel). -/
theorem wp_replyWrite1Replica (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (q : w32) (rp : Loc) (g : src.gryffproto.Write1Reply) (o : Out)
    (outs : List Out) (ho : model.sendTo q (.write1Reply (write1ReplyOf g)) = some o) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
        genericOk γ ρ k r gR h ∗ □ h1Fixed r gR ∗ rp ↦ g ∗ pendingOuts γ ρ k r t (o :: outs) }}
      (App (App (repM r go!"replyWrite1Replica") (Val #q)) (Val #rp))
    {{ RET #(); pendingOuts γ ρ k r t outs }} := by
  obtain ⟨d, rfl, rfl⟩ := sendTo_some q _ o ho
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, #HgR, #HId, #Hgen, #Hfix, Hrp, Hpend⟩ HΦ
  ihave Hm : msgAt rp (.write1Reply (write1ReplyOf g)) $$ [Hrp]
  · iapply (msgAt_write1Reply rp _).2; iexists g; iframe; ipureintro; rfl
  wp_method_call
  wp_call
  wp_auto
  wp_if_destruct
  · have hdk := rid32_inj d k Hif
    subst d
    icases (isReplica_open ..).1 $$ Hrep with ⟨%gR1, %h1, Hex, #HgR1, -, -, -, -, -, -, Hch, -⟩
    icases (isExec_open ..).1 $$ Hex with ⟨%gR2, %mtx, %ex, %pp, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, #Hinv, -⟩ -- H-X-4: one more slot (Shutdown)
    unfold replicaChans
    icases Hch with ⟨-, -, -, -, -, -, Hb, -⟩
    unfold bagAt
    icases Hb with ⟨%ch, #Hchf, #Hbag⟩
    ihave Hup := pendingOuts_self γ ρ k r t _ outs ⊤ (fun p hp => CoPset.subseteq_top p hp)
      $$ [$Hinv $Hpend]
    iapply fupd_wp
    imod Hup with ⟨%j, Hpend, Htok⟩
    imodintro
    wp_auto
    wp_apply (wp_bag_send (ρ.chans "write1Reply") ch _ (msgChanP γ ρ k "write1Reply")) $$
      [$Hbag Hm Htok]
    · unfold msgChanP
      iexists rp, _
      iframe Hm
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      · iexists k, j; iexact Htok
    iapply HΦ; iexact Hpend
  · have hdk : d ≠ k := fun e => Hif (by rw [e])
    unfold h1Fixed
    icases Hfix with ⟨%st, %cR1, %cR2, %cW1, %cW2, %cR1R, %cR2R, %cW1R, %cW2R, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, #Hc, #Hrc, -⟩
    ihave #Hpg : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr $$ []
    · iPkgInit
    have hsend := Replica.SendMsg.wp γ ρ k d r gR h t (.write1Reply (write1ReplyOf g)) rp cW1R
      outs hdk
    simp only [msgKind, msgTy] at hsend
    wp_auto
    wp_method_call
    wp_auto
    wp_apply hsend $$ [$Hpg $Hgen $HgR $Hrc $Hm $Hpend] as ⟨-, Hpend⟩
    iapply HΦ; iexact Hpend

/-- `replyWrite2Replica(q, rp)`: the owed reply goes to `q` (itself: its channel). -/
theorem wp_replyWrite2Replica (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (q : w32) (rp : Loc) (g : src.gryffproto.Write2Reply) (o : Out)
    (outs : List Out) (ho : model.sendTo q (.write2Reply (write2ReplyOf g)) = some o) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗
        genericOk γ ρ k r gR h ∗ □ h1Fixed r gR ∗ rp ↦ g ∗ pendingOuts γ ρ k r t (o :: outs) }}
      (App (App (repM r go!"replyWrite2Replica") (Val #q)) (Val #rp))
    {{ RET #(); pendingOuts γ ρ k r t outs }} := by
  obtain ⟨d, rfl, rfl⟩ := sendTo_some q _ o ho
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, #HgR, #HId, #Hgen, #Hfix, Hrp, Hpend⟩ HΦ
  ihave Hm : msgAt rp (.write2Reply (write2ReplyOf g)) $$ [Hrp]
  · iapply (msgAt_write2Reply rp _).2; iexists g; iframe; ipureintro; rfl
  wp_method_call
  wp_call
  wp_auto
  wp_if_destruct
  · have hdk := rid32_inj d k Hif
    subst d
    icases (isReplica_open ..).1 $$ Hrep with ⟨%gR1, %h1, Hex, #HgR1, -, -, -, -, -, -, Hch, -⟩
    icases (isExec_open ..).1 $$ Hex with ⟨%gR2, %mtx, %ex, %pp, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, #Hinv, -⟩ -- H-X-4: one more slot (Shutdown)
    unfold replicaChans
    icases Hch with ⟨-, -, -, -, -, -, -, Hb, -⟩
    unfold bagAt
    icases Hb with ⟨%ch, #Hchf, #Hbag⟩
    ihave Hup := pendingOuts_self γ ρ k r t _ outs ⊤ (fun p hp => CoPset.subseteq_top p hp)
      $$ [$Hinv $Hpend]
    iapply fupd_wp
    imod Hup with ⟨%j, Hpend, Htok⟩
    imodintro
    wp_auto
    wp_apply (wp_bag_send (ρ.chans "write2Reply") ch _ (msgChanP γ ρ k "write2Reply")) $$
      [$Hbag Hm Htok]
    · unfold msgChanP
      iexists rp, _
      iframe Hm
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      · iexists k, j; iexact Htok
    iapply HΦ; iexact Hpend
  · have hdk : d ≠ k := fun e => Hif (by rw [e])
    unfold h1Fixed
    icases Hfix with ⟨%st, %cR1, %cR2, %cW1, %cW2, %cR1R, %cR2R, %cW1R, %cW2R, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, #Hc, #Hrc⟩
    ihave #Hpg : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr $$ []
    · iPkgInit
    have hsend := Replica.SendMsg.wp γ ρ k d r gR h t (.write2Reply (write2ReplyOf g)) rp cW2R
      outs hdk
    simp only [msgKind, msgTy] at hsend
    wp_auto
    wp_method_call
    wp_auto
    wp_apply hsend $$ [$Hpg $Hgen $HgR $Hrc $Hm $Hpend] as ⟨-, Hpend⟩
    iapply HΦ; iexact Hpend

/-- **Close** after a participant step that keeps the rest (`ppf`). -/
theorem parti_close (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h pa co : Loc)
    (xs : XS) (s s' : RState) (hf : ppf s' = ppf s) (hid : s.id = rid32 k) :
    epEnv γ ρ k r gR h pa co ∗ partiOwn pa (replicaIface r) k s'.tag s'.ongoing ∗
      valOwn gR s'.val ∗ coordOwn ρ co (replicaIface r) k s ∗ epaxosOwn ρ h r xs s ∗
      ghostVar ρ.xs (1 : Qp).half xs ∗ proposeOwn ρ gR s.proposeQ ∗ scratchOwn r ⊢
      replicaOwn ρ k r s' := by
  simp only [ppf, Prod.mk.injEq] at hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hf
  iintro ⟨#Henv, Hpa, Hval, Hco, Hep, Hxs, Hprop, Hscr⟩
  iapply handler_close γ ρ k r gR h pa co xs s'
  iframe Henv
  unfold parts
  rw [h12]
  ihave Hep := epaxosOwn_congr ρ h r xs s s' h6 h7 h8 h9 h10 h11 $$ Hep
  ihave Hco := coordOwn_congr ρ co (replicaIface r) k s s' h2 h3 h4 h5 $$ Hco
  iframe Hpa Hval Hco Hep Hxs Hprop Hscr
  ipureintro; rw [h1]; exact hid

variable [pD : GryffPartiDeps (GF := GF)]

theorem handleRead1Proxied.wp_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Read1ProxiedM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleRead1Proxied") (.read1 m) := by
  intro p t s s' outs hstep
  have hst : model.stepRead1 s m = .ok (s', outs) := hstep
  obtain ⟨hf, o1, rfl⟩ := stepRead1_ppf s s' m outs hst
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hmsg⟩ HΦ
  icases g_open γ ρ k r s $$ [$Hrep $Hown] with ⟨%gR, %pa, %co, %h, %xs, #Henv, Hparts⟩
  unfold parts
  icases Hparts with ⟨Hpa, Hval, Hco, Hep, Hxs, Hprop, Hscr, %Hid⟩
  icases epEnv_fields γ ρ k r gR h pa co $$ Henv with ⟨#HgR, #Hpa', #Hco', #HId, #Hgen⟩
  ihave #Hfix := genericOk_h1Fixed γ ρ k r gR h $$ Hgen
  ihave #Hip := Replica_ipartiOk_proof r gR $$ [$Hpkg $HgR $Hfix]
  ihave #Hpc : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon $$ []
  · iPkgInit
  icases (msgAt_read1 p m).1 $$ Hmsg with ⟨%g, Hp, %Hg⟩
  subst Hg
  iStructNamedPrefix Hp "f"
  ipersist fD
  ipersist fVt
  wp_method_call
  wp_call
  wp_auto
  have hspec := (GryffPartiDeps.handleRead1 (GF := GF) (hG := hG)) pa (replicaIface r) k (valOwn (GF := GF) gR) s s' o1
    (read1Of g) (p.[src.gryffproto.Read1Proxied, go!"D"]) (p.[src.gryffproto.Read1Proxied, go!"Vt"])
    g.D' g.Vt' rfl rfl Hid hst
  simp only [read1Of] at hspec
  wp_apply hspec $$ [$Hpc $Hpa $Hip $Hval $fD $fVt] as %rp ⟨Hpa, Hval, %g', Hrp, %Ho⟩
  wp_apply (wp_replyRead1Replica γ ρ k r gR h t _ rp g' o1 [] Ho) $$
    [$Hpkg $Hrep $HgR $HId $Hgen $Hfix $Hrp $Hpend] as Hpend
  iapply HΦ
  iframe Hpend
  iapply parti_close γ ρ k r gR h pa co xs s s' hf Hid $$ [$Henv $Hpa $Hval $Hco $Hep $Hxs $Hprop $Hscr]

theorem handleRead2Proxied.wp_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Read2ProxiedM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleRead2Proxied") (.read2 m) := by
  intro p t s s' outs hstep
  have hst : model.stepRead2 s m = .ok (s', outs) := hstep
  obtain ⟨hf, o1, rfl⟩ := stepRead2_ppf s s' m outs hst
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hmsg⟩ HΦ
  icases g_open γ ρ k r s $$ [$Hrep $Hown] with ⟨%gR, %pa, %co, %h, %xs, #Henv, Hparts⟩
  unfold parts
  icases Hparts with ⟨Hpa, Hval, Hco, Hep, Hxs, Hprop, Hscr, %Hid⟩
  icases epEnv_fields γ ρ k r gR h pa co $$ Henv with ⟨#HgR, #Hpa', #Hco', #HId, #Hgen⟩
  ihave #Hfix := genericOk_h1Fixed γ ρ k r gR h $$ Hgen
  ihave #Hip := Replica_ipartiOk_proof r gR $$ [$Hpkg $HgR $Hfix]
  ihave #Hpc : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon $$ []
  · iPkgInit
  icases (msgAt_read2 p m).1 $$ Hmsg with ⟨%g, Hp, %Hg⟩
  subst Hg
  wp_method_call
  wp_call
  wp_auto
  have hspec := (GryffPartiDeps.handleRead2 (GF := GF) (hG := hG)) pa (replicaIface r) k (valOwn (GF := GF) gR) s s' o1
    (read2Of g) g.Vt' g.UpdateId' rfl hst
  simp only [read2Of] at hspec
  wp_apply hspec $$ [$Hpc $Hpa $Hip $Hval] as %rp ⟨Hpa, Hval, %g', Hrp, %Ho⟩
  wp_apply (wp_replyRead2Replica γ ρ k r gR h t _ rp g' o1 [] Ho) $$
    [$Hpkg $Hrep $HgR $HId $Hgen $Hfix $Hrp $Hpend] as Hpend
  iapply HΦ
  iframe Hpend
  iapply parti_close γ ρ k r gR h pa co xs s s' hf Hid $$ [$Henv $Hpa $Hval $Hco $Hep $Hxs $Hprop $Hscr]

theorem handleWrite2Proxied.wp_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Write2ProxiedM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleWrite2Proxied") (.write2 m) := by
  intro p t s s' outs hstep
  have hst : model.stepWrite2 s m = .ok (s', outs) := hstep
  obtain ⟨hf, o1, rfl⟩ := stepWrite2_ppf s s' m outs hst
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hmsg⟩ HΦ
  icases g_open γ ρ k r s $$ [$Hrep $Hown] with ⟨%gR, %pa, %co, %h, %xs, #Henv, Hparts⟩
  unfold parts
  icases Hparts with ⟨Hpa, Hval, Hco, Hep, Hxs, Hprop, Hscr, %Hid⟩
  icases epEnv_fields γ ρ k r gR h pa co $$ Henv with ⟨#HgR, #Hpa', #Hco', #HId, #Hgen⟩
  ihave #Hfix := genericOk_h1Fixed γ ρ k r gR h $$ Hgen
  ihave #Hip := Replica_ipartiOk_proof r gR $$ [$Hpkg $HgR $Hfix]
  ihave #Hpc : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon $$ []
  · iPkgInit
  icases (msgAt_write2 p m).1 $$ Hmsg with ⟨%g, Hp, %Hg⟩
  subst Hg
  wp_method_call
  wp_call
  wp_auto
  have hspec := (GryffPartiDeps.handleWrite2 (GF := GF) (hG := hG)) pa (replicaIface r) k (valOwn (GF := GF) gR) s s' o1
    (write2Of g) g.Vt' rfl Hid hst
  simp only [write2Of] at hspec
  wp_apply hspec $$ [$Hpc $Hpa $Hip $Hval] as %rp ⟨Hpa, Hval, %g', Hrp, %Ho⟩
  wp_apply (wp_replyWrite2Replica γ ρ k r gR h t _ rp g' o1 [] Ho) $$
    [$Hpkg $Hrep $HgR $HId $Hgen $Hfix $Hrp $Hpend] as Hpend
  iapply HΦ
  iframe Hpend
  iapply parti_close γ ρ k r gR h pa co xs s s' hf Hid $$ [$Henv $Hpa $Hval $Hco $Hep $Hxs $Hprop $Hscr]

theorem handleWrite1Proxied.wp_proof (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc)
    (m : model.Write1ProxiedM) :
    msgHandlerSpec γ ρ k r (repM r go!"handleWrite1Proxied") (.write1 m) := by
  intro p t s s' outs hstep
  have hst : model.stepWrite1 s m = .ok (s', outs) := hstep
  have hf := stepWrite1_ppf s s' m outs hst
  simp only [repM]
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hmsg⟩ HΦ
  icases g_open γ ρ k r s $$ [$Hrep $Hown] with ⟨%gR, %pa, %co, %h, %xs, #Henv, Hparts⟩
  unfold parts
  icases Hparts with ⟨Hpa, Hval, Hco, Hep, Hxs, Hprop, Hscr, %Hid⟩
  icases epEnv_fields γ ρ k r gR h pa co $$ Henv with ⟨#HgR, #Hpa', #Hco', #HId, #Hgen⟩
  ihave #Hfix := genericOk_h1Fixed γ ρ k r gR h $$ Hgen
  ihave #Hip := Replica_ipartiOk_proof r gR $$ [$Hpkg $HgR $Hfix]
  ihave #Hpc : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon $$ []
  · iPkgInit
  icases (msgAt_write1 p m).1 $$ Hmsg with ⟨%g, Hp, %Hg⟩
  subst Hg
  iStructNamedPrefix Hp "f"
  ipersist fD
  ipersist fMaxAppliedTag
  wp_method_call
  wp_call
  wp_auto
  have hspec := (GryffPartiDeps.handleWrite1 (GF := GF) (hG := hG)) pa (replicaIface r) k (valOwn (GF := GF) gR) s s'
    outs (write1Of g) g.V' g.N' (p.[src.gryffproto.Write1Proxied, go!"D"])
    (p.[src.gryffproto.Write1Proxied, go!"MaxAppliedTag"]) g.D' g.MaxAppliedTag' rfl Hid hst
  simp only [write1Of] at hspec
  wp_apply hspec $$ [$Hpc $Hpa $Hip $Hval $fD $fMaxAppliedTag] as %rp ⟨Hpa, Hval, Hor⟩
  icases Hor with (%Hn | ⟨%g', %o1, Hrp, %Ho⟩)
  · obtain ⟨rfl, rfl⟩ := Hn
    try wp_auto
    iapply HΦ
    iframe Hpend
    iapply parti_close γ ρ k r gR h pa co xs s s' hf Hid $$
      [$Henv $Hpa $Hval $Hco $Hep $Hxs $Hprop $Hscr]
  · obtain ⟨rfl, Ho⟩ := Ho
    ihave %Hnn := typedPointsto_not_null $$ Hrp
    try wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    · wp_apply (wp_replyWrite1Replica γ ρ k r gR h t _ rp g' o1 [] Ho) $$
        [$Hpkg $Hrep $HgR $HId $Hgen $Hfix $Hrp $Hpend] as Hpend
      iapply HΦ
      iframe Hpend
      iapply parti_close γ ρ k r gR h pa co xs s s' hf Hid $$
        [$Henv $Hpa $Hval $Hco $Hep $Hxs $Hprop $Hscr]

end

end Perennial.gryff.replica2

/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/SendMsg.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: `genericsmr.(*Replica).SendMsg` (proof of `Replica2/Specs.lean`'s `Replica.SendMsg.wp`)
-/
module

public import Dsverify.Proof.gryff.N.StateLaws
public import Dsverify.Proof.gryff.N.Marshal
public import Dsverify.Proof.gryff.N.ArrLen
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (Msg Out)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
-- beyond `Replica2/Specs.lean`'s section (hub request N-1): the node's extra assumptions that
-- `Marshal` / `Unmarshal` (`Wire/Specs.lean`) need
variable [wire.BinaryVarintHyps GF]


/-- A message to send: its encoding after the code (`msgWire`), its `Marshal` (`marSpec`) with
its resources `R`, and the way back to `msgAt`. -/
theorem msgAt_send (p : Loc) (m : Msg) (code : w8)
    (hc : netN.kindCode (msgKind m) = some code) :
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
        isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ msgAt p m ⊢
      ∃ (e : List w8) (R : IProp GF), ⌜msgWire m (code :: e) ∧ netN.marSpec (msgTy m) p e R⌝ ∗
        R ∗ (R -∗ msgAt p m) := by
  unfold msgAt
  cases m with
  | read1 mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, Ho, %Hpr⟩
    iexists wire.gryffproto.Read1Proxied.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Read1Proxied.own p (DFrac.own 1) g)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_Read1Proxied p g⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho⟩
    iexists g; iframe Ho; ipureintro; exact Hpr
  | read2 mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, Ho, %Hpr⟩
    iexists wire.gryffproto.Read2Proxied.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Read2Proxied.own p (DFrac.own 1) g)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_Read2Proxied p g⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho⟩
    iexists g; iframe Ho; ipureintro; exact Hpr
  | read1Reply mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, Ho, %Hpr⟩
    iexists wire.gryffproto.Read1Reply.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Read1Reply.own p (DFrac.own 1) g)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_Read1Reply p g⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho⟩
    iexists g; iframe Ho; ipureintro; exact Hpr
  | read2Reply mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, Ho, %Hpr⟩
    iexists wire.gryffproto.Read2Reply.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Read2Reply.own p (DFrac.own 1) g)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_Read2Reply p g⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho⟩
    iexists g; iframe Ho; ipureintro; exact Hpr
  | write1 mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, Ho, %Hpr⟩
    iexists wire.gryffproto.Write1Proxied.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Write1Proxied.own p (DFrac.own 1) g)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_Write1Proxied p g⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho⟩
    iexists g; iframe Ho; ipureintro; exact Hpr
  | write2 mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, Ho, %Hpr⟩
    iexists wire.gryffproto.Write2Proxied.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Write2Proxied.own p (DFrac.own 1) g)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_Write2Proxied p g⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho⟩
    iexists g; iframe Ho; ipureintro; exact Hpr
  | write1Reply mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, Ho, %Hpr⟩
    iexists wire.gryffproto.Write1Reply.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Write1Reply.own p (DFrac.own 1) g)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_Write1Reply p g⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho⟩
    iexists g; iframe Ho; ipureintro; exact Hpr
  | write2Reply mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, Ho, %Hpr⟩
    iexists wire.gryffproto.Write2Reply.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Write2Reply.own p (DFrac.own 1) g)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_Write2Reply p g⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho⟩
    iexists g; iframe Ho; ipureintro; exact Hpr
  | preAccept mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, %sl, Ho, #Hs, %Hpr⟩
    ihave ⟨⟨Ho, -⟩, %Hl⟩ := netN.preAccept_len2 _ _ _ _ $$ [$Ho $Hs]
    iexists wire.gryffproto.PreAccept.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ p ↦ wire.gryffproto.PreAccept.goVal g sl ∗
      sl ↦*□ g.Command)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_PreAccept p g sl⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hl.1, Hl.2, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho, -⟩
    iexists g, sl; iframe Ho Hs; ipureintro; exact Hpr
  | preAcceptReply mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, Ho, %Hpr⟩
    ihave ⟨Ho, %Hl⟩ := netN.preAcceptReply_len _ _ _ $$ Ho
    iexists wire.gryffproto.PreAcceptReply.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.PreAcceptReply.own p (DFrac.own 1) g)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_PreAcceptReply p g⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hl.1, Hl.2, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho⟩
    iexists g; iframe Ho; ipureintro; exact Hpr
  | preAcceptOK mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, Ho, %Hpr⟩
    iexists wire.epaxosproto.PreAcceptOK.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.epaxosproto.PreAcceptOK.own p (DFrac.own 1) g)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_PreAcceptOK p g⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho⟩
    iexists g; iframe Ho; ipureintro; exact Hpr
  | accept mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, %sl, Ho, #Hs, %Hpr⟩
    ihave ⟨⟨Ho, -⟩, %Hl⟩ := netN.accept_len2 _ _ _ _ $$ [$Ho $Hs]
    iexists wire.gryffproto.EAccept.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ p ↦ wire.gryffproto.EAccept.goVal g sl ∗
      sl ↦*□ g.Command)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_EAccept p g sl⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hl.1, Hl.2, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho, -⟩
    iexists g, sl; iframe Ho Hs; ipureintro; exact Hpr
  | acceptReply mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, Ho, %Hpr⟩
    iexists wire.epaxosproto.AcceptReply.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.epaxosproto.AcceptReply.own p (DFrac.own 1) g)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_AcceptReply p g⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho⟩
    iexists g; iframe Ho; ipureintro; exact Hpr
  | commit mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, %sl, Ho, #Hs, %Hpr⟩
    ihave ⟨⟨Ho, -⟩, %Hl⟩ := netN.commit_len2 _ _ _ _ $$ [$Ho $Hs]
    iexists wire.gryffproto.ECommit.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ p ↦ wire.gryffproto.ECommit.goVal g sl ∗
      sl ↦*□ g.Command)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_ECommit p g sl⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hl.1, Hl.2, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho, -⟩
    iexists g, sl; iframe Ho Hs; ipureintro; exact Hpr
  | prepare mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, Ho, %Hpr⟩
    iexists wire.epaxosproto.Prepare.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.epaxosproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.epaxosproto.Prepare.own p (DFrac.own 1) g)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_Prepare p g⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho⟩
    iexists g; iframe Ho; ipureintro; exact Hpr
  | prepareReply mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, %sl, Ho, #Hs, %Hpr⟩
    ihave ⟨⟨Ho, -⟩, %Hl⟩ := netN.prepareReply_len2 _ _ _ _ $$ [$Ho $Hs]
    iexists wire.gryffproto.PrepareReply.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ p ↦ wire.gryffproto.PrepareReply.goVal g sl ∗
      sl ↦*□ g.Command)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_PrepareReply p g sl⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hl.1, Hl.2, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho, -⟩
    iexists g, sl; iframe Ho Hs; ipureintro; exact Hpr
  | executed mm =>
    obtain rfl := Option.some.inj ((by rfl : netN.kindCode _ = _).symm.trans hc)
    dsimp only
    iintro ⟨#Hg, #He, #Hb, %g, Ho, %Hpr⟩
    iexists wire.gryffproto.Executed.enc g, iprop(isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗ wire.gryffproto.Executed.own p (DFrac.own 1) g)
    isplitr
    · ipureintro
      refine ⟨?_, netN.marSpec_Executed p g⟩
      rw [msgWire_eq]
      exact ⟨g, rfl, Hpr⟩
    iframe Ho; iframe #
    iintro ⟨-, -, Ho⟩
    iexists g; iframe Ho; ipureintro; exact Hpr
  | executeOverwrite mm => simp [msgKind, netN.kindCode] at hc

/-- **`SendMsg(q, code, m)`**: `Replica2/Specs.lean`'s `Replica.SendMsg.wp`, with the node's
extra assumptions (hub request N-1). -/
theorem SendMsg_wp (γ : GryffNames GF) (ρ : Repl2Names) (k q : Fin 3) (r gR h : Loc)
    (t : List model.Ev) (m : Msg) (p : Loc) (code : w8) (outs : List Out) (hq : q ≠ k) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ genericOk γ ρ k r gR h ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ rpcCodeIs (msgKind m) code ∗ msgAt p m ∗
        pendingOuts γ ρ k r t (.send q m :: outs) }}
      (App (App (App (Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!! go!"SendMsg"))
        (Val #(rid32 q))) (Val #code))
        (Val #(interface.mkOk (msgTy m) #p)))
    {{ RET #(); msgAt p m ∗ pendingOuts γ ρ k r t outs }} := by
  iintro %Φ ⟨#Hpkg, #Hgen, #HgR, Hcode, Hm, Hpo⟩ HΦ
  ihave %Hcode := rpcCodeIs_elim _ _ $$ Hcode
  ihave ⟨#HId, #Hgp, #Hep⟩ := genericOk_send $$ Hgen
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hdl : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
  · iPkgInit
  ihave #Hdlog := replica.dlog_init_access $$ Hdl
  ihave Hpo := (pendingOuts_unfold ..).1 $$ Hpo
  icases Hpo with ⟨Hnet, Hdone⟩
  iunfold netAt at Hnet
  icases Hnet with ⟨%gR', %pwS, %pws, #HgR', #Hpw, #HpwS, Hpeers, Hself, Hcl, #Htlb, #Hal⟩
  icombine HgR HgR' gives %Heq
  subst Heq
  -- the peer's writer
  ihave ⟨Hq, Hpeers⟩ := bigSepL_acc_upd (peers k) (peers_nodup k) q (mem_peers k q hq)
    (fun q' => iprop(∃ (w : Loc) (ms : List Msg),
      ⌜pws[q'.val]? = some w ∧ ms ++ sentToR q' (.send q m :: outs) = streamOf k q' t⌝ ∗
      peerWriterAt γ k q' w ms))
    (fun q' => iprop(∃ (w : Loc) (ms : List Msg),
      ⌜pws[q'.val]? = some w ∧ ms ++ sentToR q' outs = streamOf k q' t⌝ ∗
      peerWriterAt γ k q' w ms))
    (fun q' hq' => by rw [sentToR_send_other q q' m outs hq']) $$ Hpeers
  icases Hq with ⟨%w, %ms, %Hwms, Hpwq⟩
  ihave Hpwq := (peerWriterAt_unfold ..).1 $$ Hpwq
  iunfold netN.peerWriterB at Hpwq
  icases Hpwq with ⟨%wr, %J, %Q, %hdr, %W, %sent, %pend, %err, #Hwr, Hown, %Hst, #Hbr,
    ⟨%ws, #Hpred⟩⟩
  -- the delay map
  ihave Hcl := (clientsOwn_unfold ..).1 $$ Hcl
  icases Hcl with ⟨Hesc, %dS, %dms, #Hd, #HdS, %Hdl3, Hmaps⟩
  obtain ⟨mp, hmp⟩ : ∃ mp, dms[q.val]? = some mp :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hdl3]; exact q.isLt)⟩
  ihave ⟨⟨%M, Hmp, %HM⟩, Hmaps⟩ := BigSepL.bigSepL_insert_acc hmp $$ Hmaps
  -- the message
  ihave ⟨%e, %R, %He, HR, Hclose⟩ := msgAt_send p m code Hcode $$ [$Hgp $Hep $Hbufio $Hm]
  have hpre : ms ++ [m] <+: streamOf k q t := by
    rw [← Hwms.2, sentToR_send_self]; exact ⟨sentToR q outs, by simp⟩
  ihave #Hps := peerStream_send γ.proto k q ws t ms m W (code :: e) hpre Hst.1 He.1
    $$ [$Hpred $Htlb]
  ihave #HQ := Hbr $$ Hps
  have hw : pws[q.val]? = some w := Hwms.1
  rw [show rid32 q = W32 (q.val : Int) from rfl]
  wp_apply (netN.wp_SendMsg_gen gR q.val q.isLt code (msgTy m) p dS dms mp M hmp HM pwS pws w hw
    (rid32 k) wr J Q (hdr ++ W) e R He.2) $$ [Hmp Hown HR] as ⟨Hmp, HR, Hw⟩
  · iframe Hmp HR
    iframe #
    isplitl [Hown]
    · unfold netN.wAt
      iexists sent, pend, err
      iframe Hown
      ipureintro; exact ⟨Hst.2.1, Hst.2.2⟩
    rw [List.append_assoc]; iexact HQ
  iapply HΦ
  isplitl [HR Hclose]
  · iapply Hclose $$ HR
  iapply (pendingOuts_unfold ..).2
  rw [extsIn_send]
  iframe Hdone
  iunfold netAt
  iexists gR, pwS, pws
  iframe HgR Hpw HpwS Htlb Hal
  isplitl [Hpeers Hw]
  · iapply Hpeers
    iexists w, ms ++ [m]
    isplitr
    · ipureintro
      refine ⟨hw, ?_⟩
      rw [List.append_assoc, List.singleton_append, ← sentToR_send_self]; exact Hwms.2
    iapply (peerWriterAt_unfold ..).2
    iunfold netN.peerWriterB
    unfold netN.wAt
    icases Hw with ⟨%sent', %pend', %err', Hown, %Hst'⟩
    iexists wr, J, Q, hdr, W ++ code :: e, sent', pend', err'
    iframe Hwr Hown Hbr
    isplitr
    · ipureintro
      refine ⟨msgsWire_snoc Hst.1 He.1, ?_, ?_⟩
      · rw [← List.append_assoc]; exact Hst'.1
      · intro h0; rw [← List.append_assoc]; exact Hst'.2 h0
    iexists ws; iexact Hpred
  isplitl [Hself]
  · rw [show (fun q_1 => sentToR q_1 (kahn.Out.send q m :: outs)) k = sentToR k outs from
      sentToR_send_other q k m outs (Ne.symm hq)]
    iexact Hself
  iapply (clientsOwn_unfold ..).2
  iframe Hesc
  iexists dS, dms
  iframe Hd HdS
  isplitr
  · ipureintro; exact Hdl3
  have hset : dms.set q.val mp = dms := by
    obtain ⟨h1, h2⟩ := List.getElem?_eq_some_iff.1 hmp
    rw [← h2]; exact List.set_getElem_self h1
  ihave Hm2 := Hmaps $$ [Hmp]
  · iexists _
    iframe Hmp
    ipureintro
    intro c b hcb
    by_cases hc : c = code
    · subst hc; simp at hcb; exact hcb
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hc)] at hcb; exact HM c b hcb
  rw [hset]
  iexact Hm2

end

end Perennial.gryff.replica2

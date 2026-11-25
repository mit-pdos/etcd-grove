/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/Reply.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: the client replies (`CompleteRead`, `CompleteWrite`, `completeRMWWriter`)

The writer of client `cid` (`writerIs ρ cid w`) is the lock's (`clientsOwn`) once claimed: the
first reply to `cid` claims it from the escrow invariant (`genericOk`), leaving the claim token
`ghostMapElem (escrowName ρ) cid 1 w` there (`claim_writer`).
-/
module

public import Dsverify.Proof.gryff.N.SendMsg
public import Dsverify.Proof.gryff.N.Register
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (Msg Out Ext)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [wire.BinaryVarintHyps GF]


/-- What the replies read of `genericOk`: the escrow invariant, `r.maxSeenTag`. -/
theorem genericOk_reply (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) :
    genericOk γ ρ k r gR h ⊢
      inv netN.escrowN iprop(∃ WM : GMap w32 Loc, ghostMapAuth ρ.writers (1 : Qp).half WM ∗
        [∗map] hs ↦ w ∈ WM, netN.clientWriterB γ hs w ∨
          ghostMapElem (escrowName ρ) hs (DFrac.own 1) w) ∗
      (∃ tg : src.gryffproto.Tag, r.[src.gryff.Replica, go!"maxSeenTag"] ↦□ tg) ∗
      isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffproto := by
  iintro #H
  ihave #Hf := genericOk_fixed γ ρ k r gR h $$ H
  iunfold genericOk at H
  icases H with ⟨%rt, %ct, %st, %mu, %cwm, %crm, %M, %CM, -, -, -, -, -, -, -, -, -, -, -, -,
    #Hinv, -, -, -, #Hg, -, -⟩
  unfold genericFixed
  icases Hf with ⟨%pS, %alS, %addrs, %st', %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    %cP, %cPR, %cR1, %cR2, %cW1, %cW2, %cR1R, %cR2R, %cW1R, %cW2R,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Htg⟩
  iframe #

instance writerIs_persistent' (ρ : Repl2Names) (c : w32) (w : Loc) :
    Persistent (writerIs ρ c w : IProp GF) := by
  unfold writerIs; infer_instance

theorem writerIs_agree (ρ : Repl2Names) (c : w32) (w w' : Loc) :
    writerIs ρ c w ∗ writerIs ρ c w' ⊢ (⌜w = w'⌝ : IProp GF) := by
  unfold writerIs
  iintro ⟨H1, H2⟩
  iapply ghostMapElem_agree $$ H1 H2

/-- **Claiming client `cid`'s writer** (the lock's `clientsOwn`): taken from the escrow
invariant the first time (a later credit strips the invariant's later). -/
theorem claim_writer (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (gR : Loc) (cid : w32)
    (w : Loc) :
    inv netN.escrowN iprop(∃ WM : GMap w32 Loc, ghostMapAuth ρ.writers (1 : Qp).half WM ∗
        [∗map] hs ↦ w ∈ WM, netN.clientWriterB γ hs w ∨
          ghostMapElem (escrowName ρ) hs (DFrac.own 1) w) ∗
      writerIs ρ cid w ∗ clientsOwn γ ρ k gR ∗ £ 1 ⊢
      |={⊤}=> netN.clientWriterB γ cid w ∗ (netN.clientWriterB γ cid w -∗ clientsOwn γ ρ k gR) := by
  iintro ⟨#Hinv, #Hw, Hcl, Hlc⟩
  ihave Hcl := (clientsOwn_unfold ..).1 $$ Hcl
  icases Hcl with ⟨⟨%C, HC, Hmap⟩, Hdel⟩
  cases hC : C !! cid with
  | some w' =>
    ihave ⟨⟨#Hw', Hb⟩, Hmap⟩ := (BigSepM.bigSepM_delete hC).1 $$ Hmap
    ihave %Hag := writerIs_agree ρ cid w w' $$ [Hw Hw']
    · iframe #
    subst Hag
    imodintro
    iframe Hb
    iintro Hb
    iapply (clientsOwn_unfold ..).2
    iframe Hdel
    iexists C; iframe HC
    iapply (BigSepM.bigSepM_delete hC).2
    iframe Hmap Hb Hw
  | none =>
    iinv Hinv with Hi Hclose
    icases Hi with ⟨%WM, >HA, Hm⟩
    ihave %HWM : ⌜WM !! cid = some w⌝ $$ [HA]
    · unfold writerIs; iapply ghost_map_lookup $$ HA Hw
    imod lc_fupd_elim_later $$ Hlc Hm with Hm
    ihave ⟨Hb, Hm⟩ := (BigSepM.bigSepM_delete HWM).1 $$ Hm
    icases Hb with (Hb | Htok)
    · imod ghost_map_insert cid w hC $$ HC with ⟨HC, Htok⟩
      imod Hclose $$ [HA Hm Htok]
      · inext
        iexists WM; iframe HA
        iapply (BigSepM.bigSepM_delete HWM).2
        iframe Hm
        iright; iexact Htok
      imodintro
      iframe Hb
      iintro Hb
      iapply (clientsOwn_unfold ..).2
      iframe Hdel
      iexists (C.insert cid w); iframe HC
      iapply (BigSepM.bigSepM_insert hC).2
      iframe Hmap Hb Hw
    · ihave %Hc := ghost_map_lookup $$ HC Htok
      exact absurd (hC.symm.trans Hc) (by simp)

theorem extsIn_ext (x : Ext) (o : List Out) : pure.extsIn (.ext x :: o) = x :: pure.extsIn o := by
  simp [pure.extsIn]

theorem sentToR_ext (q : Fin 3) (x : Ext) (o : List Out) :
    sentToR q (.ext x :: o) = sentToR q o := by
  unfold sentToR kahn.sentTo
  apply List.filterMap_cons_none
  rfl

theorem msgsOk_snoc (ok : List w8 → IProp GF) (X m : List w8) (hm : m ≠ []) :
    msgsOk ok X ∗ ok m ⊢ msgsOk ok (X ++ m) := by
  unfold msgsOk
  iintro ⟨⟨%ms, %Hms, Hl⟩, Hm⟩
  iexists ms ++ [m]
  isplitr
  · ipureintro
    refine ⟨by rw [Hms.1]; simp, fun x hx => ?_⟩
    rcases List.mem_append.1 hx with h | h
    · exact Hms.2 x h
    · rw [List.mem_singleton.1 h]; exact hm
  iapply (BigSepL.bigSepL_snoc).2
  iframe Hl Hm

/-- A client writer about to take reply `c :: e` (allowed: `clientReplyOk`): its state, the
stream with the reply allowed, and the way back once the writer has been handed the reply. -/
instance clientReplyOk_persistent' (γ : GryffNames GF) (cid : w32) (m : List w8) :
    Persistent (clientReplyOk γ cid m) := by
  unfold clientReplyOk; infer_instance

theorem writer_pre (γ : GryffNames GF) (cid : w32) (w : Loc) (c : w8) (e : List w8) :
    netN.clientWriterB γ cid w ∗ clientReplyOk γ cid (c :: e) ⊢
      ∃ (wr : wire.WSt GF) (J Q : List w8 → IProp GF) (X sent pend : List w8) (err : GoInterface),
        wire.writerOk wr J Q ∗ wire.ownWriter w wr J Q sent pend err ∗
        ⌜sent ++ pend <+: X ∧ (err = interface.nil → pend = [] ∧ sent = X)⌝ ∗
        □ Q (X ++ c :: e) ∗
        (∀ (s p : List w8) (er : GoInterface), wire.ownWriter w wr J Q s p er -∗
          ⌜s ++ p <+: X ++ c :: e ∧ (er = interface.nil → p = [] ∧ s = X ++ c :: e)⌝ -∗
          netN.clientWriterB γ cid w) := by
  iintro ⟨Hb, #Hrep⟩
  iunfold netN.clientWriterB at Hb
  icases Hb with ⟨%wr, %J, %Q, %X, %sent, %pend, %err, #Hwr, Hown, %Hst, #HX, #HQ⟩
  ihave #HX' : □ msgsOk (clientReplyOk γ cid) (X ++ c :: e) $$ []
  · imodintro
    iapply msgsOk_snoc (clientReplyOk γ cid) X (c :: e) (by simp)
    iframe #
  ihave #HQX := HQ $$ HX'
  iexists wr, J, Q, X, sent, pend, err
  iframe Hwr Hown HQX
  isplitr
  · ipureintro; exact Hst
  iintro %s %p %er Hown %Hs
  iunfold netN.clientWriterB
  iexists wr, J, Q, X ++ c :: e, s, p, er
  iframe Hwr Hown HX' HQ
  ipureintro; exact Hs

set_option goose.wp.extras true

theorem wp_Replica_Printf (r : Loc) (f : GoString) (v : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog ∗
        globalAddr gryff.src.dlog.DLOG ↦□ false }}
      (App (App (Val (r @!! go.GoType.PointerType src.gryff.Replica.ty @!! go!"Printf")) (Val #f))
        (Val #v))
    {{ RET #(); True }} := by
  wp_start as #Hd
  wp_auto
  wp_end

theorem CompleteRead_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List model.Ev) (cid rid : w32) (w : Loc) (v : w64) (outs : List Out) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ genericOk γ ρ k r gR h ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ writerIs ρ cid w ∗
        pendingOuts γ ρ k r t (.ext (.readReply cid rid v (W8 1)) :: outs) }}
      (App (App (App (App (Val (r @!! go.GoType.PointerType src.gryff.Replica.ty @!! go!"CompleteRead"))
        (Val #rid)) (Val #cid)) (Val #true)) (Val #v))
    {{ RET #(); pendingOuts γ ρ k r t outs }} := by
  wp_start as ⟨#Hgen, #HgR, #Hw, Hpo⟩
  ihave ⟨#Hinv, ⟨%tg, #Htg⟩, #Hgp⟩ := genericOk_reply γ ρ k r gR h $$ Hgen
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hdl : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
  · iPkgInit
  ihave #Hdlog := replica.dlog_init_access $$ Hdl
  wp_auto_lc 1
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_Replica_Printf $$ [$Hdlog]
  wp_method_call
  wp_auto
  wp_apply GetClientWriter_wp γ ρ k r gR h cid w $$ [$Hgen $Hw]
  ihave Hpo := (pendingOuts_unfold ..).1 $$ Hpo
  icases Hpo with ⟨Hnet, Hdone⟩
  iunfold netAt at Hnet
  icases Hnet with ⟨%gR', %pwS, %pws, #HgR', #Hpw, #HpwS, Hpeers, Hself, Hcl, #Htlb, #Hal⟩
  iapply fupd_wp
  imod claim_writer γ ρ k gR' cid w $$ [$Hinv $Hw $Hcl $Hlc1] with ⟨Hb, Hback⟩
  imodintro
  rw [extsIn_ext]
  ihave ⟨Hd1, Hdone⟩ := BigSepL.bigSepL_cons.1 $$ Hdone
  let m0 : wire.gryffproto.ReadReply.Msg :=
    { RequestId' := rid, ClientId' := cid, V' := v, MaxSeenTag' := tg, OK' := W8 1 }
  rw [show (Ext.readReply cid rid v (W8 1)).keyZ = (sint.Z cid, sint.Z rid) from rfl,
    show (Ext.readReply cid rid v (W8 1)).out = .value v from rfl]
  ihave #Hrep := clientReplyOk_intro γ cid rid (.value v) (W8 25 :: wire.gryffproto.ReadReply.enc m0)
    (Or.inl ⟨m0, v, rfl, rfl, rfl, rfl, rfl, rfl⟩) $$ Hd1
  ihave ⟨%wr, %J, %Q, %X, %sent, %pend, %err, #Hwr, Hown, %Hst, #HQ, Hcls⟩ :=
    writer_pre γ cid w (W8 25) _ $$ [$Hb $Hrep]
  ihave #Hpc := netN.writerOk_prefixClosed $$ Hwr
  ihave #HQc := EtcdGrove.bufio.Q_of_prefix Q (X ++ [W8 25]) (X ++ W8 25 :: wire.gryffproto.ReadReply.enc m0)
    (by simp) $$ Hpc HQ
  wp_apply netN.wp_WriteByte_any w wr J Q sent pend X err (W8 25) Hst $$ [$Hwr $Hown $HQc]
    as %e1 ⟨%s1, %p1, Hown, %H1⟩
  ihave Hwst := netN.wst_of_own w wr J Q s1 p1 e1 ((X ++ [W8 25]).drop (s1 ++ p1).length)
    (fun he => by rw [H1.2 he]; simp) $$ Hown
  wp_apply wire.gryffproto.ReadReply.wp_Marshal_gen «$r0_ptr» (DFrac.own 1) m0 w wr J Q s1 p1 e1
    ((X ++ [W8 25]).drop (s1 ++ p1).length ++ wire.gryffproto.ReadReply.enc m0)
    ((X ++ [W8 25]).drop (s1 ++ p1).length) $$ [$Hwr $Hwst «$r0»] as ⟨Hwst, «$r0»⟩
  · isplitr
    · obtain ⟨z, hz⟩ := H1.1
      have : s1 ++ p1 ++ ((X ++ [W8 25]).drop (s1 ++ p1).length ++ wire.gryffproto.ReadReply.enc m0) =
          X ++ W8 25 :: wire.gryffproto.ReadReply.enc m0 := by
        rw [← hz, List.drop_left, ← List.append_assoc, hz]; simp
      rw [this]; iexact HQ
    · isplitr
      · ipureintro; exact List.prefix_refl _
      · iexact «$r0»
  iunfold wire.wst at Hwst
  icases Hwst with ⟨%k2, %s2, %p2, %e2, %H2, Hown⟩
  wp_apply wire.wp_Flush w wr J Q s2 p2 e2 $$ [$Hown] as %e3 ⟨%k3, %H3, Hown⟩
  have hf := netN.sendmsg_final X (wire.gryffproto.ReadReply.enc m0) s1 p1 s2 p2 _ (W8 25) e1 e2 e3
    k2 k3 H1.1 H1.2 rfl H2.2.1 H2.2.2.2.1 H2.2.2.2.2 H3.2.1 H3.2.2
  ihave Hb := Hcls $$ Hown %hf
  ihave Hcl := Hback $$ Hb
  iapply HΦ
  iapply (pendingOuts_unfold ..).2
  iframe Hdone
  iunfold netAt
  iexists gR', pwS, pws
  simp only [sentToR_ext]
  iframe
  iframe #

theorem CompleteWrite_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List model.Ev) (cid rid : w32) (w : Loc) (outs : List Out) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ genericOk γ ρ k r gR h ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ writerIs ρ cid w ∗
        pendingOuts γ ρ k r t (.ext (.writeReply cid rid (W8 1)) :: outs) }}
      (App (App (App (Val (r @!! go.GoType.PointerType src.gryff.Replica.ty @!! go!"CompleteWrite"))
        (Val #rid)) (Val #cid)) (Val #true))
    {{ RET #(); pendingOuts γ ρ k r t outs }} := by
  wp_start as ⟨#Hgen, #HgR, #Hw, Hpo⟩
  ihave ⟨#Hinv, ⟨%tg, #Htg⟩, #Hgp⟩ := genericOk_reply γ ρ k r gR h $$ Hgen
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hdl : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
  · iPkgInit
  ihave #Hdlog := replica.dlog_init_access $$ Hdl
  wp_auto_lc 1
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_Replica_Printf $$ [$Hdlog]
  wp_method_call
  wp_auto
  wp_apply GetClientWriter_wp γ ρ k r gR h cid w $$ [$Hgen $Hw]
  ihave Hpo := (pendingOuts_unfold ..).1 $$ Hpo
  icases Hpo with ⟨Hnet, Hdone⟩
  iunfold netAt at Hnet
  icases Hnet with ⟨%gR', %pwS, %pws, #HgR', #Hpw, #HpwS, Hpeers, Hself, Hcl, #Htlb, #Hal⟩
  iapply fupd_wp
  imod claim_writer γ ρ k gR' cid w $$ [$Hinv $Hw $Hcl $Hlc1] with ⟨Hb, Hback⟩
  imodintro
  rw [extsIn_ext]
  ihave ⟨Hd1, Hdone⟩ := BigSepL.bigSepL_cons.1 $$ Hdone
  let m0 : wire.gryffproto.WriteReply.Msg :=
    { RequestId' := rid, ClientId' := cid, MaxSeenTag' := tg, OK' := W8 1 }
  rw [show (Ext.writeReply cid rid (W8 1)).keyZ = (sint.Z cid, sint.Z rid) from rfl,
    show (Ext.writeReply cid rid (W8 1)).out = .done from rfl]
  ihave #Hrep := clientReplyOk_intro γ cid rid .done (W8 27 :: wire.gryffproto.WriteReply.enc m0)
    (Or.inr (Or.inl ⟨m0, rfl, rfl, rfl, rfl, rfl⟩)) $$ Hd1
  ihave ⟨%wr, %J, %Q, %X, %sent, %pend, %err, #Hwr, Hown, %Hst, #HQ, Hcls⟩ :=
    writer_pre γ cid w (W8 27) _ $$ [$Hb $Hrep]
  ihave #Hpc := netN.writerOk_prefixClosed $$ Hwr
  ihave #HQc := EtcdGrove.bufio.Q_of_prefix Q (X ++ [W8 27]) (X ++ W8 27 :: wire.gryffproto.WriteReply.enc m0)
    (by simp) $$ Hpc HQ
  wp_apply netN.wp_WriteByte_any w wr J Q sent pend X err (W8 27) Hst $$ [$Hwr $Hown $HQc]
    as %e1 ⟨%s1, %p1, Hown, %H1⟩
  ihave Hwst := netN.wst_of_own w wr J Q s1 p1 e1 ((X ++ [W8 27]).drop (s1 ++ p1).length)
    (fun he => by rw [H1.2 he]; simp) $$ Hown
  wp_apply wire.gryffproto.WriteReply.wp_Marshal_gen «$r0_ptr» (DFrac.own 1) m0 w wr J Q s1 p1 e1
    ((X ++ [W8 27]).drop (s1 ++ p1).length ++ wire.gryffproto.WriteReply.enc m0)
    ((X ++ [W8 27]).drop (s1 ++ p1).length) $$ [$Hwr $Hwst «$r0»] as ⟨Hwst, «$r0»⟩
  · isplitr
    · obtain ⟨z, hz⟩ := H1.1
      have : s1 ++ p1 ++ ((X ++ [W8 27]).drop (s1 ++ p1).length ++ wire.gryffproto.WriteReply.enc m0) =
          X ++ W8 27 :: wire.gryffproto.WriteReply.enc m0 := by
        rw [← hz, List.drop_left, ← List.append_assoc, hz]; simp
      rw [this]; iexact HQ
    · isplitr
      · ipureintro; exact List.prefix_refl _
      · iexact «$r0»
  iunfold wire.wst at Hwst
  icases Hwst with ⟨%k2, %s2, %p2, %e2, %H2, Hown⟩
  wp_apply wire.wp_Flush w wr J Q s2 p2 e2 $$ [$Hown] as %e3 ⟨%k3, %H3, Hown⟩
  have hf := netN.sendmsg_final X (wire.gryffproto.WriteReply.enc m0) s1 p1 s2 p2 _ (W8 27) e1 e2 e3
    k2 k3 H1.1 H1.2 rfl H2.2.1 H2.2.2.2.1 H2.2.2.2.2 H3.2.1 H3.2.2
  ihave Hb := Hcls $$ Hown %hf
  ihave Hcl := Hback $$ Hb
  iapply HΦ
  iapply (pendingOuts_unfold ..).2
  iframe Hdone
  iunfold netAt
  iexists gR', pwS, pws
  simp only [sentToR_ext]
  iframe
  iframe #

theorem completeRMWWriter_wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List model.Ev) (cid rid : w32) (w : Loc) (v : w64) (outs : List Out) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ genericOk γ ρ k r gR h ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ writerIs ρ cid w ∗
        pendingOuts γ ρ k r t (.ext (.rmwReply cid rid (W8 1)) :: outs) }}
      (App (App (App (Val (r @!! go.GoType.PointerType src.gryff.Replica.ty @!! go!"completeRMWWriter"))
        (Val #rid)) (Val #w)) (Val #v))
    {{ RET #(); pendingOuts γ ρ k r t outs }} := by
  wp_start as ⟨#Hgen, #HgR, #Hw, Hpo⟩
  ihave ⟨#Hinv, ⟨%tg, #Htg⟩, #Hgp⟩ := genericOk_reply γ ρ k r gR h $$ Hgen
  ihave ⟨#HId, -, -⟩ := genericOk_send γ ρ k r gR h $$ Hgen
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hdl : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
  · iPkgInit
  ihave #Hdlog := replica.dlog_init_access $$ Hdl
  wp_auto_lc 1
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply replica.wp_dlog_Printf $$ [$Hdlog]
  wp_method_call
  wp_auto
  ihave Hpo := (pendingOuts_unfold ..).1 $$ Hpo
  icases Hpo with ⟨Hnet, Hdone⟩
  iunfold netAt at Hnet
  icases Hnet with ⟨%gR', %pwS, %pws, #HgR', #Hpw, #HpwS, Hpeers, Hself, Hcl, #Htlb, #Hal⟩
  iapply fupd_wp
  imod claim_writer γ ρ k gR' cid w $$ [$Hinv $Hw $Hcl $Hlc1] with ⟨Hb, Hback⟩
  imodintro
  rw [extsIn_ext]
  ihave ⟨Hd1, Hdone⟩ := BigSepL.bigSepL_cons.1 $$ Hdone
  let m0 : wire.gryffproto.RMWReply.Msg :=
    { RequestId' := rid, ReplicaId' := rid32 k, OldValue' := v, OK' := W8 1 }
  rw [show (Ext.rmwReply cid rid (W8 1)).keyZ = (sint.Z cid, sint.Z rid) from rfl,
    show (Ext.rmwReply cid rid (W8 1)).out = .done from rfl]
  ihave #Hrep := clientReplyOk_intro γ cid rid .done (W8 23 :: wire.gryffproto.RMWReply.enc m0)
    (Or.inr (Or.inr ⟨m0, rfl, rfl, rfl, rfl⟩)) $$ Hd1
  ihave ⟨%wr, %J, %Q, %X, %sent, %pend, %err, #Hwr, Hown, %Hst, #HQ, Hcls⟩ :=
    writer_pre γ cid w (W8 23) _ $$ [$Hb $Hrep]
  ihave #Hpc := netN.writerOk_prefixClosed $$ Hwr
  ihave #HQc := EtcdGrove.bufio.Q_of_prefix Q (X ++ [W8 23]) (X ++ W8 23 :: wire.gryffproto.RMWReply.enc m0)
    (by simp) $$ Hpc HQ
  wp_apply netN.wp_WriteByte_any w wr J Q sent pend X err (W8 23) Hst $$ [$Hwr $Hown $HQc]
    as %e1 ⟨%s1, %p1, Hown, %H1⟩
  ihave Hwst := netN.wst_of_own w wr J Q s1 p1 e1 ((X ++ [W8 23]).drop (s1 ++ p1).length)
    (fun he => by rw [H1.2 he]; simp) $$ Hown
  wp_apply wire.gryffproto.RMWReply.wp_Marshal_gen «$r0_ptr» (DFrac.own 1) m0 w wr J Q s1 p1 e1
    ((X ++ [W8 23]).drop (s1 ++ p1).length ++ wire.gryffproto.RMWReply.enc m0)
    ((X ++ [W8 23]).drop (s1 ++ p1).length) $$ [$Hwr $Hwst «$r0»] as ⟨Hwst, «$r0»⟩
  · isplitr
    · obtain ⟨z, hz⟩ := H1.1
      have : s1 ++ p1 ++ ((X ++ [W8 23]).drop (s1 ++ p1).length ++ wire.gryffproto.RMWReply.enc m0) =
          X ++ W8 23 :: wire.gryffproto.RMWReply.enc m0 := by
        rw [← hz, List.drop_left, ← List.append_assoc, hz]; simp
      rw [this]; iexact HQ
    · isplitr
      · ipureintro; exact List.prefix_refl _
      · iexact «$r0»
  iunfold wire.wst at Hwst
  icases Hwst with ⟨%k2, %s2, %p2, %e2, %H2, Hown⟩
  wp_apply wire.wp_Flush w wr J Q s2 p2 e2 $$ [$Hown] as %e3 ⟨%k3, %H3, Hown⟩
  have hf := netN.sendmsg_final X (wire.gryffproto.RMWReply.enc m0) s1 p1 s2 p2 _ (W8 23) e1 e2 e3
    k2 k3 H1.1 H1.2 rfl H2.2.1 H2.2.2.2.1 H2.2.2.2.2 H3.2.1 H3.2.2
  ihave Hb := Hcls $$ Hown %hf
  ihave Hcl := Hback $$ Hb
  iapply HΦ
  iapply (pendingOuts_unfold ..).2
  iframe Hdone
  iunfold netAt
  iexists gR', pwS, pws
  simp only [sentToR_ext]
  iframe
  iframe #

end

end Perennial.gryff.replica2

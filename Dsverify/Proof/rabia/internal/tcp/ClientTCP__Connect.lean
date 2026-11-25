/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/ClientTCP__Connect.lean`,
run `rabia-r1wake-1`, onto `Net/`'s connections (`net.Dial`, `dial_au`, `close_au`) and the revised
bufio (`rdOwn`/`wrOwn`, `Basics.lean`). The protocol facts of what the reader returned come one
step later (`rdOwn_proto`): a later credit each.)

The proof of `rabia/internal/tcp.(*ClientTCP).Connect`: `connect` (the dial/handshake retry loop,
setting `estab` when the handshake write succeeds) and the client's two routines.
-/
module

public import Dsverify.Proof.rabia.internal.tcp.Hub
public import Dsverify.Proof.rabia.internal.tcp.Frames
public import Net.Spec.net.Dial
public import Net.Spec.net.Conn__Close

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false


namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia
  rabia.internal.message rabia.internal.config

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

/-- Client `c` establishes its connection `cid` to proxy `k` (once: its token). -/
theorem estab_set (γ : Names) (c k : Nat) (cid : Nat) :
    inv estabN (estabInv (GF := GF) γ) ∗ estabTok γ c k ⊢ |={⊤}=> estab γ c k cid := by
  iintro ⟨#Hinv, Htok⟩
  unfold estabInv
  iinv Hinv with ⟨%m, >Ha⟩ Hclose
  unfold estabTok
  imod ghost_map_update (some cid) $$ Ha Htok with ⟨Ha, Htok⟩
  imod ghostMapElem_persist $$ Htok with #Hp
  imod Hclose $$ [Ha] with -
  · inext; iexists _; iexact Ha
  imodintro
  unfold estab
  iexact Hp

/-- The next frame a client reads from its proxy is a `Command`'s encoding. -/
theorem proxyQ_frameIs (γ : Names) (k : Nat) (cid : Nat) (rs : List CmdV)
    (hrs : ∀ r ∈ rs, (encCmd r).length < 2 ^ 32) :
    ⊢ frameIs (proxyQ (GF := GF) γ k) cid (frames (rs.map encCmd))
      (fun bs => ∃ c, bs = encCmd c) := by
  unfold frameIs
  imodintro
  iintro %bs %hbs Hp
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HQ⟩)
  · ipureintro
    exfalso
    have := congrArg List.length Hnil
    simp [frame_length] at this
  have hne : ext ≠ [] := by
    intro h; subst h
    have := Hext.length_le
    simp [frame_length] at this
  ihave ⟨%c, %rs', -, %Hp, -⟩ := proxyQ_hub γ k cid ext hne $$ HQ
  ipureintro
  obtain ⟨-, hext, hb⟩ := Hp
  have hpre := frames_decomp (A := rs.map encCmd) (L := rs'.map encCmd) (b := bs) (X := [])
    (by simpa using hrs) (by simpa using hb) hbs (by simpa using Hext.trans hext)
  have hget := prefix_snoc_getElem hpre
  have hmem : bs ∈ rs'.map encCmd := List.mem_of_getElem? hget
  obtain ⟨r, -, hr⟩ := List.mem_map.1 hmem
  exact ⟨r, hr.symm⟩

/-- A reply read from the proxy is one to the connection's client. -/
theorem proxyQ_read (γ : Names) (k : Nat) (cid : Nat) (c : Nat) (hc : c < nC) (rs : List CmdV)
    (hrs : ∀ r ∈ rs, (encCmd r).length < 2 ^ 32) (q : CmdV) (hq : (encCmd q).length < 2 ^ 32) :
    protoPrefix (proxyQ (GF := GF) γ k) cid (frames (rs.map encCmd) ++ model.frame (encCmd q)) ∗
      sentLb (Gg := hG.goose_globalGS) cid false (hsBytes c) ⊢ repOk γ c q := by
  iintro ⟨Hp, #Hs⟩
  unfold protoPrefix
  icases Hp with (%Hnil | ⟨%ext, %Hext, #HQ⟩)
  · iexfalso; ipureintro
    have := congrArg List.length Hnil
    simp [frame_length] at this
  have hne : ext ≠ [] := by
    intro h; subst h
    have := Hext.length_le
    simp [frame_length] at this
  ihave ⟨%c', %rs', #Hs', %Hp, #Hreps⟩ := proxyQ_hub γ k cid ext hne $$ HQ
  obtain ⟨hc', hext, hb⟩ := Hp
  ihave %Hcmp := sentLb_agree cid false (hsBytes c) (hsBytes c') $$ [$Hs $Hs']
  have hcc : c = c' := hsBytes_inj c c' (by unfold nC at hc; omega) (by unfold nC at hc'; omega) Hcmp
  subst hcc
  have hpre := frames_decomp (A := rs.map encCmd) (L := rs'.map encCmd) (b := encCmd q) (X := [])
    (by simpa using hrs) (by simpa using hb) hq (by simpa using Hext.trans hext)
  have hget := prefix_snoc_getElem hpre
  simp only [List.getElem?_map, List.length_map] at hget
  rcases h : rs'[rs.length]? with _ | r
  · simp [h] at hget
  simp only [h, Option.map_some, Option.some.injEq] at hget
  have hqr : q = r := encCmd_inj hget.symm
  subst hqr
  iapply (BigSepL.bigSepL_lookup (i := rs.length) h) $$ Hreps

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.internal.tcp.Assumptions] [sync.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions]
variable [net.Assumptions] [go.BasicIntoValInj]
variable [msg_sem : rabia.internal.message.Assumptions]

set_option goose.wp.extras true

theorem wp_ClientTCP_RecvHandler (D : TcpDeps (GF := GF)) (γ : Names) (cf : RCfg) (c : Nat) (γc : ClNames) (t : Loc) (hc : c < nC)
    (br : Loc) (cid : Nat) (rc : GoChan) (wg : Loc) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗
      t.[ClientTCP, go!"Reader"] ↦□ br ∗ t.[ClientTCP, go!"RecvChan"] ↦□ rc ∗
      isChanBag γc.recv rc (repP γ c) ∗ t.[ClientTCP, go!"Wg"] ↦□ wg ∗ wgTok wg ∗
      rdOwn br cid false (proxyQ γ (c % cf.n)) [] ∗
      sentLb (Gg := hG.goose_globalGS) cid false (hsBytes c) }}
    (App (Val (t @!! go.GoType.PointerType ClientTCP.ty @!! go!"RecvHandler")) (Val #()))
  {{ RET #(); True }} := by
  wp_start as ⟨#HR, #HRC, #Hbag, #HWg, Htok, Hbr, #Hs⟩
  ihave #Hmpkg : (isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message) $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply (wp_slice_make2 (V := w8) _) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  ihave %Hsl0 := ownSlice_len _ _ _ $$ Hsl
  have hsl : sint.nat sl.len = 409600 := by rw [← Hsl0.1, List.length_replicate]
  ihave HI : (∃ (rs : List CmdV) (ds : List w8), "Hsl" ∷ sl ↦* ds ∗
      "Hbr" ∷ rdOwn br cid false (proxyQ γ (c % cf.n)) (frames (rs.map encCmd)) ∗
      "%Hrs" ∷ ⌜∀ r ∈ rs, (encCmd r).length < 2 ^ 32⌝ : IProp GF) $$ [Hsl Hbr]
  · iexists [], _
    iframe
    ipureintro; simp
  wp_for HI
  ihave %Hdl := ownSlice_len _ _ _ $$ Hsl
  have hdl : ds.length = 409600 := by rw [Hdl.1, hsl]
  ihave #HF := proxyQ_frameIs γ (c % cf.n) cid rs Hrs
  wp_apply wp_cmdReadUnmarshal D cmd_ptr br cid false _ _ sl ds $$ [$Hmpkg $cmd $Hbr $HF $Hsl]
    as %e ⟨%ds', Hsl, Hres⟩
  icases Hres with (⟨%He, %v, %q, %Hq, Hcmd, #Hrep, Hbr⟩ | ⟨%He, %R', %v, %HR', Hcmd, Hbr⟩)
  · subst He
    have Hq : (encCmd q).length < 2 ^ 32 := by omega
    ihave ⟨Hbr, Hp⟩ := rdOwn_proto br cid false _ _ $$ Hbr
    wp_auto_lc 1
    iapply fupd_wp
    imod (lc_fupd_elim_later (GF := GF) (E := ⊤)) $$ Hlc1 Hp with #Hp
    ihave #Hrepq := proxyQ_read γ (c % cf.n) cid c hc rs Hrs q Hq $$ [$Hp $Hs]
    imodintro
    wp_apply wp_bag_send γc.recv rc v (repP γ c) $$ [$Hbag]
    · unfold repP; iexists q; iframe #
    wp_for_post
    iframe
    iexists rs ++ [q], ds'
    simp only [List.map_append, List.map_cons, List.map_nil, frames_append, frames_cons, frames_nil,
      List.append_nil]
    iframe
    ipureintro
    intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact Hrs r hr
    · exact Hq
  · rcases e with ei | _
    · wp_auto
      wp_for_post
      wp_apply wp_wgDone wg $$ [$Htok]
      iapply HΦ
      itrivial
    · exact absurd rfl He

theorem wp_ClientTCP_SendHandler (D : TcpDeps (GF := GF)) (γ : Names) (cf : RCfg) (c : Nat) (γc : ClNames) (t : Loc) (hc : c < nC)
    (bw : Loc) (cid : Nat) (sc done : GoChan) (wg : Loc) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗
      t.[ClientTCP, go!"Writer"] ↦□ bw ∗ t.[ClientTCP, go!"SendChan"] ↦□ sc ∗
      isSpsc γc.send sc (clSendP γ c) (fun _ => iprop(False)) ∗
      t.[ClientTCP, go!"Done"] ↦□ done ∗ doneChan done ∗
      t.[ClientTCP, go!"Wg"] ↦□ wg ∗ wgTok wg ∗ spscConsumer γc.send ([] : List Command) ∗
      wrOwn bw cid false (proxyP γ (c % cf.n)) (hsBytes c) [] interface.nil ∗
      estab γ c (c % cf.n) cid ∗ cfgIs γ.rab cf }}
    (App (Val (t @!! go.GoType.PointerType ClientTCP.ty @!! go!"SendHandler")) (Val #()))
  {{ RET #(); True }} := by
  wp_start as ⟨#HW, #HSC, #Hspsc, #HD, #Hdone, #HWg, Htok, Hcons, Hw, #Hest, #Hcf⟩
  ihave #Hmpkg : (isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message) $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer Hdefer
  unfold doneChan
  icases Hdone with ⟨%γd, #Hdbag⟩
  ihave HI : (∃ (qs : List CmdV) (vs : List Command), "Hcons" ∷ spscConsumer γc.send vs ∗
      "Hw" ∷ wrOwn bw cid false (proxyP γ (c % cf.n))
        (hsBytes c ++ frames (qs.map encCmd)) [] interface.nil ∗
      "%Hq" ∷ ⌜qs.Pairwise (fun a b => a.cliSeq.toNat < b.cliSeq.toNat) ∧
        (∀ q ∈ qs, q.cliSeq.toNat < vs.length ∧ (encCmd q).length < 2 ^ 32) ∧
        qs.length ≤ vs.length ∧ vs.length ≤ opBudget⌝ ∗
      "#Hreqs" ∷ [∗list] q ∈ qs, reqOk γ c q : IProp GF) $$ [Hcons Hw]
  · iexists [], []
    simp only [List.map_nil, frames_nil, List.append_nil]
    iframe
    isplitr
    · ipureintro; simp [opBudget]
    iapply BigSepL.bigSepL_nil.2; iempintro
  wp_for_core
  iNamed HI
  wp_auto_lc 1
  irename Hlc1 => Hlc2
  cleanup_bool_decide
  wp_auto_lc 1
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `Done`: nothing is sent
    dsimp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, done, γd
    isplitr
    · ipureintro; rfl
    ihave #Hdch := is_bag_is_chan _ _ _ $$ Hdbag
    iframe Hdch
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hdbag
    inext
    iintro %v Hv
    unfold doneP
    iexfalso; iexact Hv
  iapply BigAndL.bigAndL_cons.2
  isplit
  · dsimp only [chan.blockingClausePre]
    iexists Command, inferInstance, inferInstance, inferInstance, inferInstance, sc, γc.send.chanName
    isplitr
    · ipureintro; rfl
    ihave #Hsch : isChan sc γc.send.chanName Command $$ [Hspsc]
    · unfold isSpsc; icases Hspsc with ⟨$, -⟩
    iframe Hsch
    iapply spsc_rcv_au $$ Hspsc [$Hlc1 $Hlc2] Hcons
    inext
    iintro %v %ok Hv
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hv with ⟨Hv, -⟩
      iexfalso; iexact Hv
    simp only [↓reduceIte]
    icases Hv with ⟨Hv, Hcons⟩
    unfold clSendP
    icases Hv with ⟨%q, %Hqv, #Hrep, #Hreq⟩
    wp_auto
    ipersist req
    ihave #Hreq' := Hreq
    iunfold reqOk at Hreq'
    icases Hreq' with ⟨%cmd, %Hcmd, -⟩
    have hcl : q.commands.length ≤ 1 := by rw [Hcmd.2.1]; simp
    obtain ⟨hpw, hqb, hql, hvb⟩ := Hq
    have hseq : q.cliSeq.toNat = vs.length := by
      obtain ⟨h1, -, -⟩ := Hqv; rw [h1]; simp
    have hbud : vs.length < opBudget := by
      obtain ⟨-, h2, -⟩ := Hqv; simpa using h2
    have hpw' : (qs ++ [q]).Pairwise (fun a b => a.cliSeq.toNat < b.cliSeq.toNat) := by
      rw [List.pairwise_append]
      refine ⟨hpw, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb; subst hb
      rw [hseq]; exact (hqb a ha).1
    have hW : hsBytes c ++ frames (qs.map encCmd) ++ [] ++ model.frame (encCmd q) =
        hsBytes c ++ frames ((qs ++ [q]).map encCmd) := by
      simp [frames_append, frames_cons, frames_nil]
    wp_apply wp_cmdMarshalWriteFlush D req_ptr v q bw cid false _ _ [] _
      $$ [$Hmpkg $req $Hrep $Hw] as %e ⟨%sent', %pend', %Hs, Hw⟩
    · isplitr
      · ipureintro; exact hcl
      imodintro
      iintro %Hlen
      rw [hW]
      unfold proxyP
      iright
      iexists cf, c, qs ++ [q]
      isplitr
      · iexact Hcf
      isplitr
      · ipureintro
        refine ⟨hc, rfl, List.prefix_refl _, by simp; omega, hpw', ?_⟩
        intro r hr
        simp only [List.mem_append, List.mem_singleton] at hr
        rcases hr with hr | rfl
        · exact ⟨by have := (hqb r hr).1; omega, (hqb r hr).2⟩
        · exact ⟨by omega, Hlen⟩
      isplitr
      · iright; iexact Hest
      iapply BigSepL.bigSepL_snoc.2
      iframe #
    rcases e with ei | _
    · -- the write failed: the routine ends
      wp_auto
      wp_for_post
      wp_apply wp_wgDone wg $$ [$Htok]
      iapply HΦ
      itrivial
    · obtain ⟨hs0, hs⟩ := Hs
      rcases hs with ⟨hlen, -, hnil⟩ | ⟨hlen, hpre⟩
      · obtain ⟨rfl, rfl⟩ := hnil rfl
        wp_auto
        wp_for_post
        iframe
        iexists qs ++ [q], vs ++ [v]
        rw [hW]
        iframe
        isplitr
        · ipureintro
          refine ⟨hpw', ?_, by simp; omega, by simp; omega⟩
          intro r hr
          simp only [List.mem_append, List.mem_singleton, List.length_append, List.length_singleton] at hr ⊢
          rcases hr with hr | rfl
          · exact ⟨by have := (hqb r hr).1; omega, (hqb r hr).2⟩
          · exact ⟨by omega, hlen⟩
        iapply BigSepL.bigSepL_snoc.2
        iframe #
      · -- not framed (G12): nothing written
        have h1 : sent' = hsBytes c ++ frames (qs.map encCmd) ∧ pend' = [] := by
          simp only [List.append_nil] at hpre
          exact prefix_squeeze hs0 hpre
        obtain ⟨rfl, rfl⟩ := h1
        wp_auto
        wp_for_post
        iframe
        iexists qs, vs ++ [v]
        iframe
        isplitr
        · ipureintro
          refine ⟨hpw, ?_, by simp; omega, by simp; omega⟩
          intro r hr
          simp only [List.length_append, List.length_singleton]
          exact ⟨by have := (hqb r hr).1; omega, (hqb r hr).2⟩
        iframe #
  iapply BigAndL.bigAndL_nil.2
  itrivial

theorem wp_ClientTCP_connect (D : TcpDeps (GF := GF)) (γ : Names) (cf : RCfg) (c : Nat) (γc : ClNames) (t : Loc) (hc : c < nC) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗ confRO cf ∗ shared γ ∗ cfgIs γ.rab cf ∗
      clientOwn γ c γc t (proxyAddr (c % cf.n)) ∗ estabTok γ c (c % cf.n) }}
    (App (Val (t @!! go.GoType.PointerType ClientTCP.ty @!! go!"connect")) (Val #()))
  {{ RET #(); True }} := by
  wp_start as ⟨#Hconf, #Hsh, #Hcf, Hown, Htok⟩
  ihave %Hok := cfgIs_ok γ.rab cf $$ Hcf
  ihave #Hmpkg : (isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message) $$ []
  · iPkgInit
  unfold clientOwn
  icases Hown with ⟨%wg, %done, %cn, %rd, %wr, #HId, #HWg, Hwg, #HDone, #Hdone, #HAddr, HConn,
    HReader, HWriter, Hcons, #Hchans⟩
  have hk : c % cf.n < maxS :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (RCfg.n_pos cf Hok)) (RCfg.n_le_maxS cf Hok)
  ihave #Hproto := shared_proxyProto γ (c % cf.n) hk $$ Hsh
  ihave %Haok := addrTok_ok (proxyAddr (c % cf.n)) $$ [Hproto]
  · iapply addrProto_tok $$ Hproto
  wp_auto
  ihave HI : (∃ (cn rd wr : Loc), "HConn" ∷ t.[ClientTCP, go!"Conn"] ↦ cn ∗
      "HReader" ∷ t.[ClientTCP, go!"Reader"] ↦ rd ∗ "HWriter" ∷ t.[ClientTCP, go!"Writer"] ↦ wr : IProp GF)
    $$ [HConn HReader HWriter]
  · iexists cn, rd, wr; iframe
  wp_for HI
  ihave #HnetPk : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · solve_pkg_init
  wp_apply D.dial go!"tcp" net.tcpNet_tcp (proxyAddr (c % cf.n)) iprop(True)
      (fun cid => iprop(connEnd (Gg := hG.goose_globalGS) cid false (proxyP γ (c % cf.n))
        (proxyQ γ (c % cf.n)) [] [] ∗ connFresh (Gg := hG.goose_globalGS) cid false)) $$ []
    as %cv %err (⟨%Herr, %cid, #Hcl, ⟨Hend, -⟩⟩ | ⟨-, %x, -, #Herr⟩)
  · (try iframe HnetPk)
    isplitr
    · ipureintro; exact Haok
    isplit
    · itrivial
    · iapply dial_au (proxyAddr (c % cf.n)) (proxyP γ (c % cf.n)) (proxyQ γ (c % cf.n)) $$ Hproto
  · subst Herr
    wp_auto
    ipersist conn
    iunfold connEnd at Hend
    icases Hend with ⟨Hsend, Hrecv⟩
    ihave #Hconn := sendTok_connIs cid false _ _ $$ Hsend
    ihave #HP0 := (proxyP_closed (GF := GF) γ (c % cf.n)).nil cid
    wp_apply wp_GetReaderWriter D cf conn_ptr cv cid false (proxyAddr (c % cf.n)) (proxyQ γ (c % cf.n))
      (proxyP γ (c % cf.n)) [] [] (proxyP_closed γ (c % cf.n))
      $$ [$Hconf $conn $Hcl $Hrecv $Hsend $HP0] as %br %bw ⟨Hbr, Hbw⟩
    ipersist «$r0»
    ihave #Hrep : cmdRep (Command.mk (BitVec.ofNat 32 c) 0 0 slice.nil) (hsCmd c) $$ []
    · unfold cmdRep hsCmd
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl⟩
      iapply ownSlice_nil
    ihave #HP1 : proxyP γ (c % cf.n) cid (hsBytes c) $$ []
    · unfold proxyP
      iright
      iexists cf, c, []
      isplitr
      · iexact Hcf
      isplitr
      · ipureintro
        refine ⟨hc, rfl, by simp [frames], by simp, by simp⟩
      isplitr
      · ileft; ipureintro; rfl
      iapply BigSepL.bigSepL_nil.2; iempintro
    have hlen : (encCmd (hsCmd c)).length < 2 ^ 32 := hsCmd_enc_len c (by unfold nC at hc; omega)
    wp_apply wp_cmdMarshalWriteFlush D «$r0_ptr» _ (hsCmd c) bw cid false _ [] [] _
      $$ [$Hmpkg $«$r0» $Hrep $Hbw] as %e ⟨%sent', %pend', %Hs, Hw⟩
    · isplitr
      · ipureintro; simp [hsCmd]
      simp only [List.nil_append]
      rw [← show hsBytes c = model.frame (encCmd (hsCmd c)) from rfl]
      imodintro
      iintro -
      iexact HP1
    simp only [List.nil_append] at Hs
    rw [← show hsBytes c = model.frame (encCmd (hsCmd c)) from rfl] at Hs
    have Hs2 : sent' ++ pend' <+: hsBytes c ∧ (e = interface.nil → sent' = hsBytes c ∧ pend' = []) := by
      rcases Hs.2 with h | h
      · exact h.2
      · omega
    rcases e with ei | _
    · -- the handshake write failed: close, sleep, dial again
      unfold net.isConn
      icases Hcl with ⟨%tc, %la, %ra, %Hct, #Hca⟩
      subst Hct
      wp_auto
      wp_apply D.close tc cid false _ la ra (fun _ => iprop(True)) $$ [] as %_ -
      · iframe Hca
        imod close_au cid false $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
        imodintro
        iexists st, dd
        iframe Hst Hdd
        iintro %res %st' %d' %Hd' Hst Hdd
        imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
        imodintro
        itrivial
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
      iexists _, _, _
      iframe
    · -- the handshake was written: established
      obtain ⟨rfl, rfl⟩ := Hs2.2 rfl
      imod estab_set γ c (c % cf.n) cid $$ [Htok] with #Hest
      · iframe Htok
        unfold shared
        icases Hsh with ⟨-, -, $, -⟩
      wp_auto
      wp_for_post
      ipersist HReader
      ipersist HWriter
      ihave ⟨Hw, #Hlb⟩ := wrOwn_sentLb bw cid false _ _ _ _ $$ Hw
      wp_apply wp_wgAdd wg 2 2 (by omega) (by omega) $$ [$Hwg] as ⟨-, Htoks⟩
      icases wgToks_split wg 1 $$ Htoks with ⟨Htok1, Htoks⟩
      icases wgToks_split wg 0 $$ Htoks with ⟨Htok2, -⟩
      unfold clientChans
      icases Hchans with ⟨%sc, %rc, #HSC, #HRC, #Hspsc, #Hbag⟩
      wp_apply wp_fork $$ [Hbr Htok1]
      · wp_apply wp_ClientTCP_RecvHandler D γ cf c γc t hc br cid rc wg $$ [$Hbr $Htok1]
        · iframe #
        itrivial
      wp_apply wp_fork $$ [Hw Hcons Htok2]
      · wp_apply wp_ClientTCP_SendHandler D γ cf c γc t hc bw cid sc done wg $$ [$Hw $Hcons $Htok2]
        · iframe #
        itrivial
      iapply HΦ
      itrivial
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    wp_apply time.wp_Sleep
    wp_for_post
    iframe
    iexists _, _, _
    iframe

theorem ClientTCP.Connect.wp_proof (D : TcpDeps (GF := GF)) : ClientTCP.Connect.spec (GF := GF) := by
  intro γ cf c γc t hc
  wp_start as ⟨#Hconf, #Hsh, #Hcf, Hown, Htok⟩
  wp_auto
  wp_apply wp_fork $$ [Hown Htok]
  · wp_apply wp_ClientTCP_connect D γ cf c γc t hc $$ [$Hown $Htok]
    · iframe #
    itrivial
  wp_end

end proof

end Perennial.rabia.internal.tcp

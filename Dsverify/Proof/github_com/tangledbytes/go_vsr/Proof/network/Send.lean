/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/network/Send.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension. `net.Dial` and the connection's `Close` are
the hypotheses `wp_Dial`, `wp_Close` (`net.Dial.spec`, `net.Conn.Close.spec`, with `dial_au` at a
configured address's `addrProto` and `close_au`; the lab's `net.DialNet.wp_proof`,
`net.TCPConn.Close.wp_proof`), their errors `net.resErr`s; `slog.Debug` is `wp_Debug`
(`log.slog.Debug.spec`), and the reader `handleConn` spawns takes its own (`HandleConn.lean`).
-/
/-
`TCP.Send`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.network
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.HandleConnDefs
public import Net.Spec.net.Dial

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

-- (no local `gooseInvGS` instance: the WP's update modality is `HeapGS`'s)

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

/-- The writer's token, and the connection is the library's. -/
theorem network.sendTok_connIs' (cn : Nat) (s : Bool) (P : Proto GF) (W : List w8) :
    sendTok (Gg := hG.goose_globalGS) cn s P W ⊢ sendTok cn s P W ∗ connIs cn :=
  persistent_entails_left (sendTok_connIs cn s P W)

/-- `Close` of a connection whose `Close` error is logged: any result. -/
theorem network.wp_close_conn (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (c : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    {{ net.connAt (GF := GF) c cn s a la ra ∗ connIs (Gg := hG.goose_globalGS) cn }}
      (App (Val #(methods (go.GoType.PointerType net.TCPConn.ty) go!"Close" #c)) (Val #()))
    {{ (err : GoInterface), RET #err; ∃ res, net.resErr res go!"close" la ra none
        (· = go!"close") err }} := by
  iintro %Φ ⟨#Hca, #Hconn⟩ HΦ
  iapply wp_Close c cn s a la ra (fun _ => iprop(True)) $$ []
  · iframe Hca
    imod close_au cn s $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
    imodintro
    iexists st, dd
    iframe Hst Hdd
    iintro %res %st' %d' %Hd' Hst Hdd
    imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
    imodintro
    itrivial
  iintro !> %err ⟨%res, -, #He⟩
  iapply HΦ; iexists res; iexact He

theorem network.TCP.Send.wp_proof
    (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (wp_newDecoder : events.newDecoder.spec (GF := GF) (hG := hG))
    (wp_NewNetworkEvent : events.NewNetworkEvent.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_String_ptr : ipv4port.IPv4Port.String_ptr.spec (GF := GF) (hG := hG))
    (wp_handleConn : network.TCP.handleConn.spec (GF := GF) (hG := hG)) :
    network.TCP.Send.spec (GF := GF) (hG := hG) := by
  intro tcp γ me a f R Q
  wp_start as ⟨#Htcp, Hsnd, #Haok, Hf, HR, #Hprotos⟩
  unfold network.isTCP network.isTCPDef network.tcpCore
  icases Htcp with ⟨%ns, %v, %hγ, ⟨#Hfl, #Hroot, #Hlock, #Hreg, #Hqueue⟩, #Hcfg, #Hrd, #Hnv⟩
  unfold network.tcpSender network.tcpSenderDef
  icases Hsnd with ⟨%ns', %v', %T, #Hfl', #Hroot', Hown, HT, Hpool⟩
  imod network.rootInv_agree tcp ns ns' $$ [$Hroot $Hroot'] with %hns
  subst hns
  unfold network.fieldsRO
  icases Hfl with ⟨#Hip, #Hconns, #Hsrcs, #Hq, #Hmu⟩
  icases Hfl' with ⟨#Hip', #Hconns', #Hsrcs', #Hq', #Hmu'⟩
  icombine Hip Hip' gives %e1
  icombine Hconns Hconns' gives %e2
  icombine Hsrcs Hsrcs' gives %e3
  icombine Hq Hq' gives %e4
  icombine Hmu Hmu' gives %e5
  obtain rfl : v = v' := by cases v; cases v'; simp_all
  subst hγ
  iclear Hip' Hconns' Hsrcs' Hq' Hmu' Hroot'
  wp_auto
  wp_apply wp_String_ptr $$ [$ipv4port] as ipv4port
  wp_apply wp_slice_literal (V := GoInterface)
    [interface.mkOk go.string #(go!"ipv4port"), interface.mkOk go.string #a.str']
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply network.wp_debug_wf wp_Debug _ _ _
    (fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)) $$ [$Hsl]
  wp_apply sync.RWMutex.wp_RLock $$ [$Hown] as ⟨Hrl, HP⟩
  icases HP with ⟨%mc, %ms, %D, %S, Hcm, Hsm, HD, HS, %hS, #Hent, #Hdead, #Hsrcm⟩
  wp_apply wp_String_ptr $$ [$ipv4port] as ipv4port
  wp_apply wp_map_lookup2 $$ [$Hcm] as Hcm
  wp_apply wp_String_ptr $$ [$ipv4port] as ipv4port
  wp_apply (lc := 1) wp_map_lookup1 $$ [$Hsm] as Hsm
  cases hmc : mc !! a.str' with
  | some cv =>
    ihave #He := (BigSepM.bigSepM_lookup (PROP := IProp GF)
      (Φ := fun k v => network.entryOk ns D k v) (m := mc) (i := a.str') (x := cv) hmc) $$ Hent
    icases He with ⟨%c, %x, %hcx, #Hx⟩
    obtain ⟨rfl, hxk, hcD⟩ := hcx
    imod network.take_conn ns c x _ D T hcD $$ [$Hreg $Hlc1 $Hx $HD $HT $Hpool]
      with ⟨HD, %T', %W, HT, #Hc, Hs, Hw, Hback⟩
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hcm Hsm HD HS] as Hown
    · iexists mc, ms, D, S
      iframe
      iframe Hent Hdead Hsrcm
      ipureintro; exact hS
    simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
    wp_auto
    wp_apply wp_String_ptr $$ [$ipv4port] as ipv4port
    wp_apply wp_slice_literal (V := GoInterface)
      [interface.mkOk go.string #(go!"ipv4port"), interface.mkOk go.string #a.str']
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply network.wp_debug_wf wp_Debug _ _ _
      (fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)) $$ [$Hsl2]
    icases network.sendTok_connIs' x.1 x.2.1 _ _ $$ Hs with ⟨Hs, #Hconn⟩
    ihave #Hc0 := Hc
    icases Hc0 with ⟨%ca, %cla, %cra, #Hca⟩
    ihave #Hnetp : (isPkgInit (PROP := IProp GF) pkg_id.net) $$ []
    · iPkgInit
    ihave Hws := network.wstream_of_pool ns c x W $$ [$Hnetp $Hc $Hs $Hw]
    unfold network.sendFn
    wp_apply Hf $$ [$Hws] [$HR] as %err Hws #HerrF HQ
    cases err with
    | nil =>
      wp_auto
      wp_apply wp_String_ptr $$ [$ipv4port] as ipv4port
      wp_apply wp_slice_literal (V := GoInterface)
        [interface.mkOk go.string #(go!"ipv4port"), interface.mkOk go.string #a.str']
      isplitr
      · ipureintro; rfl
      iintro %sl3 ⟨Hsl3, -⟩
      wp_apply network.wp_debug_wf wp_Debug _ _ _
        (fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)) $$ [$Hsl3]
      ihave He := network.pool_of_wstream ns c x _ $$ [$Hws $Hx $Hc]
      · ileft; ipureintro; simp
      ihave #Herr : bufio.errOrNil (GF := GF) GoInterface.nil $$ []
      · unfold bufio.errOrNil; ileft; ipureintro; rfl
      iapply HΦ
      iframe Herr
      iframe HQ
      iexists ns, v, T'
      iframe
      iframe Hip Hconns Hsrcs Hq Hmu Hroot
      iapply Hback $$ He
    | ok ii =>
      wp_auto
      wp_apply wp_slice_literal (V := GoInterface)
        [interface.mkOk go.string #(go!"err"), interface.ok ii]
      isplitr
      · ipureintro; rfl
      iintro %sl3 ⟨Hsl3, -⟩
      ihave #Herr := HerrF
      wp_apply network.wp_debug_err wp_Debug $$ [$Herr $Hsl3]
      wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hlock] as ⟨Hwl, HP⟩
      icases HP with ⟨%mc1, %ms1, %D1, %S1, Hcm, Hsm, HD, HS, %hS1, #Hent1, #Hdead1, #Hsrcm⟩
      wp_apply network.wp_close_conn wp_Close c x.1 x.2.1 ca cla cra $$ [$Hca $Hconn]
        as %cerr ⟨%cres, #Hcerr⟩
      wp_join at (if: _ then _ else _) with [err]
      · cases cerr with
        | nil => wp_auto; wp_join_done; try itrivial
        | ok ce =>
          wp_auto
          wp_apply wp_slice_literal (V := GoInterface)
            [interface.mkOk go.string #(go!"err"), interface.ok ce]
          isplitr
          · ipureintro; rfl
          iintro %sl4 ⟨Hsl4, -⟩
          wp_apply network.wp_debug_resErr wp_Debug _ _ _ cres $$ [$Hcerr $Hsl4]
          wp_join_done
      wp_join iprop(∃ mc2 : GMap GoString GoInterface, v.conns' ↦$ mc2 ∗
          ⌜mc2 !! a.str' ≠ some (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c)⌝ ∗
          ([∗map] k ↦ v ∈ mc2, network.entryOk ns D1 k v) ∗ ipv4port_ptr ↦ a ∗ tcp_ptr ↦ tcp ∗
          conn_ptr ↦ interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c)
        at (if: _ then _ else _) with [Hcm ipv4port tcp conn]
        as ⟨%mc2, Hcm, %hmc2, #Hent2, ipv4port, tcp, conn⟩
      · wp_apply wp_String_ptr $$ [$ipv4port] as ipv4port
        wp_apply wp_map_lookup1 $$ [$Hcm] as Hcm
        cases hm1 : mc1 !! a.str' with
        | none =>
          wp_auto
          wp_join_done
          iexists mc1
          iframe
          iframe Hent1
          ipureintro; rw [hm1]; simp
        | some v1 =>
          ihave #He1 := (BigSepM.bigSepM_lookup (PROP := IProp GF)
            (Φ := fun k v => network.entryOk ns D1 k v) (m := mc1) (i := a.str') (x := v1) hm1) $$ Hent1
          icases He1 with ⟨%c1, %x1, %hcx1, #Hx1⟩
          obtain ⟨rfl, -, -⟩ := hcx1
          wp_auto
          wp_if_destruct
          · wp_apply wp_String_ptr $$ [$ipv4port] as ipv4port
            wp_apply wp_mapDelete $$ [$Hcm] as Hcm
            wp_join_done
            iexists (GMap.delete a.str' mc1)
            iframe Hcm ipv4port tcp conn
            isplitr
            · ipureintro; rw [GMap.lookup_delete]; simp
            · iapply network.entries_delete $$ Hent1
          · wp_join_done
            iexists mc1
            iframe
            iframe Hent1
            ipureintro; rw [hm1]
            intro h
            simp [interface.mkOk] at h
            exact Hif (go.intoVal_inj h)
      rw [← hxk] at hmc2
      imod network.mark_dead ns D1 mc2 c x hmc2 $$ [$HD $Hdead1 $Hent2 $Hx]
        with ⟨%D2, HD, #Hdead2, #Hent3, #Hdm⟩
      wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hcm Hsm HD HS]
      · iexists mc2, ms1, D2, S1
        iframe
        iframe Hent3 Hdead2 Hsrcm
        ipureintro; exact hS1
      ihave He := network.pool_of_wstream ns c x _ $$ [$Hws $Hx $Hc]
      · iright; iexact Hdm
      iapply HΦ
      iframe Herr
      iframe HQ
      iexists ns, v, T'
      iframe
      iframe Hip Hconns Hsrcs Hq Hmu Hroot
      iapply Hback $$ He
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, _root_.decide_false, Option.getD_none]
    by_cases hacc : ms !! a.str' = some true
    · -- an accepted source whose connection has ended: `ErrNoConn`
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hcm Hsm HD HS] as Hown
      · iexists mc, ms, D, S
        iframe
        iframe Hent Hdead Hsrcm
        ipureintro; exact hS
      rw [hacc]
      simp only [Option.getD_some]
      wp_auto
      wp_apply wp_String_ptr $$ [$ipv4port] as ipv4port
      wp_apply wp_slice_literal (V := GoInterface)
        [interface.mkOk go.string #(go!"ipv4port"), interface.mkOk go.string #a.str']
      isplitr
      · ipureintro; rfl
      iintro %slE ⟨HslE, -⟩
      wp_apply network.wp_debug_wf wp_Debug _ _ _
        (fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)) $$ [$HslE]
      -- the package state: `ErrNoConn` holds `errors.New(...)`
      unfold errors.newVar
      icases Hnv with ⟨%x, #Hx, #-, #HerrS⟩
      wp_auto
      ihave #Herr : bufio.errOrNil (GF := GF)
          (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x) $$ []
      · unfold bufio.errOrNil models_lab.errAny
        iright
        isplitl
        · iexists _
          isplitr
          · ipureintro; rfl
          isplitr
          · ipureintro; go_type_set
          imodintro
          iintro %Φ' HΦ'
          iapply HerrS
          inext
          iapply HΦ'
        · ipureintro
          intro e' h T hT
          simp [interface.mkOk] at h
          subst h
          exact ⟨_, rfl⟩
      iapply HΦ
      iframe Herr
      isplitl [Hown HT Hpool]
      · iexists ns, v, T
        iframe
        iframe Hip Hconns Hsrcs Hq Hmu Hroot
      · iright
        iframe HR
        ipureintro; simp [interface.mkOk]
    · unfold network.addrOk
      imod network.cfg_of_not_src tcp ns _ S ms a a.str' hS rfl hacc $$ [$Hroot $Haok $HS]
        with ⟨%hcfg, HS⟩
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hcm Hsm HD HS] as Hown
      · iexists mc, ms, D, S
        iframe
        iframe Hent Hdead Hsrcm
        ipureintro; exact hS
      have hacc' : (ms !! a.str').getD (Perennial.zero_val Bool) = false := by
        cases h : ms !! a.str' with
        | none => rfl
        | some b => rw [h] at hacc; cases b <;> simp_all
      rw [hacc']
      wp_auto
      wp_apply wp_String_ptr $$ [$ipv4port] as ipv4port
      unfold network.netProtos VsrWire.protos
      ihave #Hpa := (BigSepL.bigSepL_mem (PROP := IProp GF)
        (Φ := fun a' => addrProto (Gg := hG.goose_globalGS) a' (VsrWire.protoOf ns.sys) (VsrWire.protoOf ns.sys))
        hcfg) $$ Hprotos
      ihave %Hok := addrTok_ok a.str' $$ [Hpa]
      · iapply addrProto_tok $$ Hpa
      wp_apply wp_Dial go!"tcp4" net.tcpNet_tcp4 a.str' iprop(True)
          (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false (VsrWire.protoOf ns.sys)
            (VsrWire.protoOf ns.sys) [] [] ∗ connFresh (Gg := hG.goose_globalGS) cn false)) $$ []
        as %cv %derr (⟨%Hderr0, %cid, #Hic, ⟨Hend, Hfr⟩⟩ | ⟨-, %dx, -, #Hderr⟩)
      · isplitr
        · ipureintro; exact Hok
        isplit
        · itrivial
        · iapply dial_au a.str' (VsrWire.protoOf ns.sys) (VsrWire.protoOf ns.sys) $$ Hpa
      · -- dialed
        subst Hderr0
        unfold net.isConn
        icases Hic with ⟨%c, %dla, %dra, %Hct, #Hca⟩
        subst Hct
        iunfold connEnd at Hend
        icases Hend with ⟨Hsend, Hrecv⟩
        icases network.sendTok_connIs' cid false _ _ $$ Hsend with ⟨Hsend, #Hconn⟩
        ihave #Hc : network.connL (GF := GF) c cid false $$ []
        · iexists a.str', dla, dra; iexact Hca
        wp_auto
        wp_apply (lc := 1) sync.RWMutex.wp_Lock_guard $$ [$Hlock] as ⟨Hwl, HP⟩
        icases HP with ⟨%mc1, %ms1, %D1, %S1, Hcm, Hsm, HD, HS, %hS1, #Hent1, #Hdead1, #Hsrcm⟩
        imod network.register_dialed ns c cid a.str' D1 T $$
          [$Hreg $Hlc1 $Hfr $Hc $Hdead1 $HT $Hpool] with ⟨#Hx, %hcD, %T', HT, Hback⟩
        wp_apply wp_String_ptr $$ [$ipv4port] as ipv4port
        wp_apply wp_mapInsert $$ [$Hcm] as Hcm
        wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hcm Hsm HD HS]
        · iexists (<[a.str' := interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c]> mc1),
            ms1, D1, S1
          iframe
          iframe Hdead1 Hsrcm
          isplitr
          · ipureintro; exact hS1
          iapply network.entries_insert $$ [$Hent1]
          iexists c, (cid, false, a.str')
          iframe Hx
          ipureintro; exact ⟨rfl, rfl, hcD⟩
        wp_apply wp_String_ptr $$ [$ipv4port] as ipv4port
        imod network.addrOkN_of_def tcp ns a $$ [$Hroot $Haok] with #HaokN
        wp_apply wp_fork $$ [Hrecv]
        · wp_apply wp_handleConn
              tcp ns v c cid false a.str' dla dra a.str' a $$ [$Hrecv]
          · unfold network.tcpCore network.fieldsRO
            iframe Hrd Hca HaokN Hroot Hlock Hreg Hqueue Hip Hconns Hsrcs Hq Hmu
          itrivial
        ihave Hw : network.wholeLines ns.sys [] $$ []
        · iapply network.wholeLines_nil
        wp_apply wp_String_ptr $$ [$ipv4port] as ipv4port
        wp_apply wp_slice_literal (V := GoInterface)
          [interface.mkOk go.string #(go!"ipv4port"), interface.mkOk go.string #a.str']
        isplitr
        · ipureintro; rfl
        iintro %sl2 ⟨Hsl2, -⟩
        wp_apply network.wp_debug_wf wp_Debug _ _ _
          (fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)) $$ [$Hsl2]
        ihave #Hnetp : (isPkgInit (PROP := IProp GF) pkg_id.net) $$ []
        · iPkgInit
        ihave Hws := network.wstream_of_pool ns c (cid, false, a.str') [] $$ [$Hnetp $Hc $Hsend $Hw]
        unfold network.sendFn
        wp_apply Hf $$ [$Hws] [$HR] as %err Hws #HerrF HQ
        cases err with
        | nil =>
          wp_auto
          wp_apply wp_String_ptr $$ [$ipv4port] as ipv4port
          wp_apply wp_slice_literal (V := GoInterface)
            [interface.mkOk go.string #(go!"ipv4port"), interface.mkOk go.string #a.str']
          isplitr
          · ipureintro; rfl
          iintro %sl3 ⟨Hsl3, -⟩
          wp_apply network.wp_debug_wf wp_Debug _ _ _
            (fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)) $$ [$Hsl3]
          ihave He := network.pool_of_wstream ns c (cid, false, a.str') _ $$ [$Hws $Hx $Hc]
          · ileft; ipureintro; simp
          ihave #Herr : bufio.errOrNil (GF := GF) GoInterface.nil $$ []
          · unfold bufio.errOrNil; ileft; ipureintro; rfl
          iapply HΦ
          iframe Herr
          iframe HQ
          iexists ns, v, T'
          iframe
          iframe Hip Hconns Hsrcs Hq Hmu Hroot
          iapply Hback $$ He
        | ok ii =>
          wp_auto
          wp_apply wp_slice_literal (V := GoInterface)
            [interface.mkOk go.string #(go!"err"), interface.ok ii]
          isplitr
          · ipureintro; rfl
          iintro %sl3 ⟨Hsl3, -⟩
          ihave #Herr := HerrF
          wp_apply network.wp_debug_err wp_Debug $$ [$Herr $Hsl3]
          wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hlock] as ⟨Hwl, HP⟩
          icases HP with ⟨%mc1, %ms1, %D1, %S1, Hcm, Hsm, HD, HS, %hS1, #Hent1, #Hdead1, #Hsrcm⟩
          wp_apply network.wp_close_conn wp_Close c cid false a.str' dla dra $$ [$Hca $Hconn]
            as %cerr ⟨%cres, #Hcerr⟩
          wp_join at (if: _ then _ else _) with [err]
          · cases cerr with
            | nil => wp_auto; wp_join_done; try itrivial
            | ok ce =>
              wp_auto
              wp_apply wp_slice_literal (V := GoInterface)
                [interface.mkOk go.string #(go!"err"), interface.ok ce]
              isplitr
              · ipureintro; rfl
              iintro %sl4 ⟨Hsl4, -⟩
              wp_apply network.wp_debug_resErr wp_Debug _ _ _ cres $$ [$Hcerr $Hsl4]
              wp_join_done
          wp_join iprop(∃ mc2 : GMap GoString GoInterface, v.conns' ↦$ mc2 ∗
              ⌜mc2 !! a.str' ≠ some (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c)⌝ ∗
              ([∗map] k ↦ v ∈ mc2, network.entryOk ns D1 k v) ∗ ipv4port_ptr ↦ a ∗ tcp_ptr ↦ tcp ∗
              conn_ptr ↦ interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c)
            at (if: _ then _ else _) with [Hcm ipv4port tcp conn]
            as ⟨%mc2, Hcm, %hmc2, #Hent2, ipv4port, tcp, conn⟩
          · wp_apply wp_String_ptr $$ [$ipv4port] as ipv4port
            wp_apply wp_map_lookup1 $$ [$Hcm] as Hcm
            cases hm1 : mc1 !! a.str' with
            | none =>
              wp_auto
              wp_join_done
              iexists mc1
              iframe
              iframe Hent1
              ipureintro; rw [hm1]; simp
            | some v1 =>
              ihave #He1 := (BigSepM.bigSepM_lookup (PROP := IProp GF)
                (Φ := fun k v => network.entryOk ns D1 k v) (m := mc1) (i := a.str') (x := v1) hm1) $$ Hent1
              icases He1 with ⟨%c1, %x1, %hcx1, #Hx1⟩
              obtain ⟨rfl, -, -⟩ := hcx1
              wp_auto
              wp_if_destruct
              · wp_apply wp_String_ptr $$ [$ipv4port] as ipv4port
                wp_apply wp_mapDelete $$ [$Hcm] as Hcm
                wp_join_done
                iexists (GMap.delete a.str' mc1)
                iframe Hcm ipv4port tcp conn
                isplitr
                · ipureintro; rw [GMap.lookup_delete]; simp
                · iapply network.entries_delete $$ Hent1
              · wp_join_done
                iexists mc1
                iframe
                iframe Hent1
                ipureintro; rw [hm1]
                intro h
                simp [interface.mkOk] at h
                exact Hif (go.intoVal_inj h)
          imod network.mark_dead ns D1 mc2 c (cid, false, a.str') hmc2 $$ [$HD $Hdead1 $Hent2 $Hx]
            with ⟨%D2, HD, #Hdead2, #Hent3, #Hdm⟩
          wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hcm Hsm HD HS]
          · iexists mc2, ms1, D2, S1
            iframe
            iframe Hent3 Hdead2 Hsrcm
            ipureintro; exact hS1
          ihave He := network.pool_of_wstream ns c (cid, false, a.str') _ $$ [$Hws $Hx $Hc]
          · iright; iexact Hdm
          iapply HΦ
          iframe Herr
          iframe HQ
          iexists ns, v, T'
          iframe
          iframe Hip Hconns Hsrcs Hq Hmu Hroot
          iapply Hback $$ He
      · -- the dial failed: `R` back
        ihave #Herr := network.resErr_errOrNil _ _ _ _ _ _ _ $$ Hderr
        icases net.resErr_netErr _ _ _ _ _ _ _ $$ Hderr with %Hne
        obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
        wp_auto
        wp_apply wp_slice_literal (V := GoInterface)
          [interface.mkOk go.string #(go!"err"), interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe]
        isplitr
        · ipureintro; rfl
        iintro %sl4 ⟨Hsl4, -⟩
        wp_apply network.wp_debug_err wp_Debug $$ [$Herr $Hsl4]
        iapply HΦ
        iframe Herr
        isplitl [Hown HT Hpool]
        · iexists ns, v, T
          iframe
          iframe Hip Hconns Hsrcs Hq Hmu Hroot
        · iright
          iframe HR
          ipureintro; simp

theorem network.Network.Send.wp_proof
    (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (wp_newDecoder : events.newDecoder.spec (GF := GF) (hG := hG))
    (wp_NewNetworkEvent : events.NewNetworkEvent.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_String_ptr : ipv4port.IPv4Port.String_ptr.spec (GF := GF) (hG := hG))
    (wp_handleConn : network.TCP.handleConn.spec (GF := GF) (hG := hG)) :
    network.Network.Send.spec (GF := GF) (hG := hG) := by
  intro n γ a f R Q
  wp_start_folded as ⟨Hn, Hs, Ha, Hf, HR, #Hprotos⟩
  unfold network.isNet network.netSender network.netAddrOk
  icases Hn with ⟨%tcp, %me, %hn, #Htcp⟩
  icases Hs with ⟨%tcp', %hn', Hs⟩
  icases Ha with ⟨%tcp'', %hn'', #Ha⟩
  subst hn
  have e1 : tcp' = tcp := by
    simp [interface.mkOk] at hn'; exact (go.intoVal_inj hn').symm
  have e2 : tcp'' = tcp := by
    simp [interface.mkOk] at hn''; exact (go.intoVal_inj hn'').symm
  subst e1 e2
  wp_pures
  wp_apply network.TCP.Send.wp_proof wp_Debug wp_newDecoder wp_NewNetworkEvent wp_Dial wp_Close
      wp_String_ptr wp_handleConn
      _ γ me a f R Q $$ [$Htcp $Hs $Ha $Hf $HR $Hprotos]
    as %err ⟨Hs, #Herr, HQ⟩
  iapply HΦ
  iframe Herr HQ
  iexists _
  iframe Hs
  ipureintro; rfl

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg

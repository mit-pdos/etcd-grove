/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/network/HandleConn.lean (lab master
915f964; notes/dsv-vr.md): over any `GF`, on the net extension. The connection is the `*TCPConn`
`c` with `net.connAt c cn s a la ra` (the lab's `net.ownTCPConn c cid side`); its `Close` is the
hypothesis `wp_Close` (`net.Conn.Close.spec`, with `close_au`: the connection is the library's,
`connIs`, taken from the reader's `recvTok` before the decoder hides it), its error a
`net.resErr`; `json.NewDecoder` is the hypothesis `wp_newDecoder` (`events.newDecoder.spec`), `events.NewNetworkEvent`
`wp_NewNetworkEvent` (the events package's spec),
`slog.Debug` the hypothesis `wp_Debug` (`log.slog.Debug.spec`).
-/
/-
`TCP.handleConn`: a connection's reader (spawned by `serve` for an accepted connection and by
`Send` for a dialed one).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.Ghost
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.queue
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.ipv4port
public import Perennial.Proof.sync.Results
public import Net.Spec.net.Conn__Close
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.HandleConnDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

theorem network.TCP.handleConn.wp_proof
    (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (wp_newDecoder : events.newDecoder.spec (GF := GF) (hG := hG))
    (wp_NewNetworkEvent : events.NewNetworkEvent.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_String_ptr : ipv4port.IPv4Port.String_ptr.spec (GF := GF) (hG := hG))
    (wp_Push : queue.Queue.Push.spec (GF := GF) (hG := hG)) :
    network.TCP.handleConn.spec (GF := GF) (hG := hG) := by
  intro tcp ns v c cid side a la ra key src
  wp_start as ⟨#Hcore, #Hrd, #Hc, Hrecv, #Hsrc⟩
  unfold network.tcpCore network.fieldsRO
  icases Hcore with ⟨⟨#Hip, #Hconns, #Hsrcs, #Hq, #Hmu⟩, #Hroot, #Hlock, #Hreg, #Hqueue⟩
  icases network.recvTok_connIs' cid side _ _ $$ Hrecv with ⟨Hrecv, #Hconn⟩
  ihave #Hic : net.isConn (GF := GF) (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c)
      cid side a $$ []
  · unfold net.isConn; iexists c, la, ra; iframe Hc; ipureintro; rfl
  wp_auto
  wp_apply wp_newDecoder ns.sys _ cid side a $$ [$Hic $Hrecv] as %dec Hdec
  · iPkgInit
  wp_for
  irename «$r0» => Hev
  ihave Hnil : slice.nil ↦* ([] : List GoInterface) $$ []
  · iapply ownSlice_nil
  wp_apply network.wp_debug_wf wp_Debug _ _ _ fmt.ArgsWf.nil $$ [$Hnil]
  unfold network.readerOk
  wp_apply Hrd $$ [$Hdec $Hev] as %err ⟨Hdec, #HerrOk, Hres⟩
  cases err with
  | nil =>
    simp only [_root_.decide_true, ite_true]
    icases Hres with ⟨%m, #Hevm, Hcap, #Hfact⟩
    unfold events.isEvent
    icases Hevm with ⟨%d, #Hevp, #Hpay⟩
    ihave Hevs : «$r0_ptr» ↦□ events.Event.mk (events.typeOf m) d $$ []
    · iexact Hevp
    iStructNamed Hevs
    wp_auto
    wp_apply wp_String_ptr $$ [$srcaddr] as srcaddr
    wp_apply wp_slice_literal (V := GoInterface)
      [interface.mkOk go.string #(go!"type"), interface.mkOk events.EventType.ty #(events.typeOf m),
        interface.mkOk go.string #(go!"from"), interface.mkOk go.string #src.str']
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply network.wp_debug_wf wp_Debug _ _ _
      (fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_int _ _ _ (network.evType_arg _)
        (fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)))) $$ [$Hsl1]
    wp_apply wp_NewNetworkEvent
    wp_apply wp_Push events.NetworkEvent.ty (network.evOk ns) $$ [$Hqueue Hcap]
    · unfold network.evOk
      iexists m
      iframe Hcap Hfact Hsrc
      unfold events.isEvent
      iexists d
      iframe Hevp Hpay
    wp_apply wp_String_ptr $$ [$srcaddr] as srcaddr
    wp_apply wp_slice_literal (V := GoInterface)
      [interface.mkOk go.string #(go!"type"), interface.mkOk events.EventType.ty #(events.typeOf m),
        interface.mkOk go.string #(go!"from"), interface.mkOk go.string #src.str']
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply network.wp_debug_wf wp_Debug _ _ _
      (fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_int _ _ _ (network.evType_arg _)
        (fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)))) $$ [$Hsl2]
    wp_for_post
    iframe

  | ok ii =>
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface)
      [interface.mkOk go.string #(go!"err"), interface.ok ii]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply network.wp_debug_err wp_Debug $$ [$HerrOk $Hsl]
    wp_for_post
    wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hlock] as ⟨Hwl, HP⟩
    icases HP with ⟨%mc1, %ms1, %D1, %S1, Hcm, Hsm, HD, HS, %hS1, #Hent1, #Hdead1, #Hsrcm⟩
    wp_apply wp_Close c cid side a la ra (fun _ => iprop(True)) $$ [] as %cerr ⟨%cres, -, #Hcerr⟩
    · iframe Hc
      imod close_au cid side $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
      imodintro
      iexists st, dd
      iframe Hst Hdd
      iintro %res %st' %d' %Hd' Hst Hdd
      imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
      imodintro
      itrivial
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
        ihave #HnetD : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
        · solve_pkg_init
        wp_apply network.wp_debug_resErr wp_Debug _ _ _ cres $$ [$HnetD $Hcerr $Hsl4]
        wp_join_done
    wp_join iprop(∃ mc2 : GMap GoString GoInterface, v.conns' ↦$ mc2 ∗
        ([∗map] k ↦ v ∈ mc2, network.entryOk ns D1 k v) ∗ key_ptr ↦ key ∗ tcp_ptr ↦ tcp ∗
        conn_ptr ↦ interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c)
      at (if: _ then _ else _) with [Hcm key tcp conn]
      as ⟨%mc2, Hcm, #Hent2, key, tcp, conn⟩
    · wp_apply wp_map_lookup1 $$ [$Hcm] as Hcm
      cases hm1 : mc1 !! key with
      | none =>
        wp_auto
        wp_join_done
        iexists mc1
        iframe
        iframe Hent1
      | some v1 =>
        ihave #He1 := (BigSepM.bigSepM_lookup (PROP := IProp GF)
          (Φ := fun k v => network.entryOk ns D1 k v) (m := mc1) (i := key) (x := v1) hm1) $$ Hent1
        icases He1 with ⟨%c1, %x1, %hcx1, #Hx1⟩
        obtain ⟨rfl, -, -⟩ := hcx1
        wp_auto
        wp_if_destruct
        · wp_apply wp_mapDelete $$ [$Hcm] as Hcm
          wp_join_done
          iexists (GMap.delete key mc1)
          iframe Hcm key tcp conn
          iapply network.entries_delete $$ Hent1
        · wp_join_done
          iexists mc1
          iframe
          iframe Hent1
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hcm Hsm HD HS]
    · iexists mc2, ms1, D1, S1
      iframe
      iframe Hent2 Hdead1 Hsrcm
      ipureintro; exact hS1
    iapply HΦ
    itrivial

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg

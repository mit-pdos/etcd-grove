/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/network/Serve.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension. `net.Listen`, `Listener.Accept`,
`Conn.RemoteAddr` are the hypotheses `wp_Listen`, `wp_Accept`, `wp_RemoteAddr` (`Net/Spec/net/`,
with `listen_au` and `accept_au` at the configured address's `addrProto`; the lab's
`net.ListenNet.wp_proof`, `net.TCPListener.Accept.wp_proof`, `net.TCPConn.RemoteAddr.wp_String`);
the listener is `net.isListener li l` with the node's `netLis l me true` (the loop's invariant),
`netLisAt l me`, instead of the lab's `net.ownListener l lid me`; the remote address's `String()` is
the Go model's `extAnyString` (`wp_TCPAddr_String`); `slog.Debug` is `wp_Debug`, and the reader
`handleConn` takes its own hypotheses.
-/
/-
`TCP.serve` (the accept loop) and `TCP.Run`.
-/
module

public import Net.Proof.net.AtAddr
public import Net.Proof.net.Errors
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.network.HandleConnDefs
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Net.Spec.net.Conn__RemoteAddr

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel



section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

/-- `(*TCPAddr).String()`: some string (the Go model's `extAnyString`). -/
theorem network.wp_TCPAddr_String (p : Loc) :
    {{ (True : IProp GF) }}
      (App (Val #(methods (go.GoType.PointerType net.TCPAddr.ty) go!"String" #p)) (Val #()))
    {{ (s : GoString), RET #s; True }} := by
  wp_start_folded as -
  wp_method_call
  wp_call
  try wp_auto
  wp_apply net.wp_extAnyString as %s
  iapply HΦ
  itrivial

/-- `tcp.serve(li)`, `li` this node's listener `l` at `me` (open): accepts connections forever
(does not return). -/
abbrev network.TCP.serve.spec : Prop :=
  ∀ (tcp : Loc) (ns : network.TcpNames) (v : network.TCP) (li : GoInterface) (l : w64)
    (me : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.network ∗
      network.tcpCore tcp ns v ∗ network.readerOk ns.sys ∗ net.isListener li l ∗
      netLis (extLocalGS netExt (L := hG.goose_localGS)) l me true ∗
      netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l me ∗
      addrProto (Gg := hG.goose_globalGS) me (VsrWire.protoOf ns.sys) (VsrWire.protoOf ns.sys) }}
    (App (Val (tcp @!! go.GoType.PointerType network.TCP.ty @!! go!"serve")) (Val #li))
  {{ (err : GoInterface), RET #err; True }}

theorem network.TCP.serve.wp_proof
    (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (wp_newDecoder : events.newDecoder.spec (GF := GF) (hG := hG))
    (wp_NewNetworkEvent : events.NewNetworkEvent.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_RemoteAddr : net.Conn.RemoteAddr.spec (GF := GF) (hG := hG))
    (wp_FromAddrString : ipv4port.FromAddrString.spec (GF := GF) (hG := hG))
    (wp_handleConn : network.TCP.handleConn.spec (GF := GF) (hG := hG)) :
    network.TCP.serve.spec (GF := GF) (hG := hG) := by
  intro tcp ns v li l me
  wp_start as ⟨#Hcore, #Hrd, #Hli, Hlis, #Hla, #Hpa⟩
  unfold network.tcpCore network.fieldsRO
  icases Hcore with ⟨⟨#Hip, #Hconns, #Hsrcs, #Hq, #Hmu⟩, #Hroot, #Hlock, #Hreg, #Hqueue⟩
  unfold net.isListener
  icases Hli with ⟨%t, %x, %Ht, #Hlt⟩
  subst Ht
  wp_auto
  ihave HI : ("Hlis" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) l me true : IProp GF)
    $$ [Hlis]
  · iframe Hlis
  wp_for HI
  wp_apply (net.Listener.Accept.spec_addrOk wp_Accept) t l x me
      (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l me true)
      (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l me true ∗
        connEnd (Gg := hG.goose_globalGS) cn true (VsrWire.protoOf ns.sys)
          (VsrWire.protoOf ns.sys) [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cn true))
      $$ [Hlis]
    as %cv %aerr (⟨%Haerr0, %cid, #Hic, Hlis, Hend, Hfr⟩ | ⟨%k, Hlis, #Haerr⟩)
  · iframe Hlt Hla
    iapply accept_au me (VsrWire.protoOf ns.sys) (VsrWire.protoOf ns.sys) _ l true $$ Hpa Hlis
  · subst Haerr0
    unfold net.isConn
    icases Hic with ⟨%c, %la, %ra, %Hct, #Hca⟩
    subst Hct
    iunfold connEnd at Hend
    icases Hend with ⟨Hsend, Hrecv⟩
    ihave #Hc : network.connL (GF := GF) c cid true $$ []
    · iexists me, la, ra; iexact Hca
    ihave #Hra : net.netAddr (GF := GF) ra $$ []
    · unfold net.connAt; icases Hca with ⟨%nw, -, -, -, #Hr, -⟩; iexact Hr
    unfold net.netAddr
    icases Hra with ⟨%rp, %rv, %hra, -⟩
    wp_auto
    wp_apply wp_RemoteAddr c cid true me la ra $$ [$Hca]
    subst hra
    wp_auto
    wp_apply network.wp_TCPAddr_String rp as %key -
    wp_apply wp_slice_literal (V := GoInterface)
      [interface.mkOk go.string #(go!"remote-addr"), interface.mkOk go.string #key]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply network.wp_debug_wf wp_Debug _ _ _
      (fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)) $$ [$Hsl]
    wp_apply (lc := 1) sync.RWMutex.wp_Lock_guard $$ [$Hlock] as ⟨Hwl, HP⟩
    icases HP with ⟨%mc1, %ms1, %D1, %S1, Hcm, Hsm, HD, HS, %hS1, #Hent1, #Hdead1, #Hsrcm⟩
    imod network.register_accepted ns c cid key D1 $$ [$Hreg $Hlc1 $Hfr $Hc $Hsend $Hdead1]
      with ⟨#Hx, %hcD⟩
    imod network.src_learn ns S1 key $$ [$HS $Hsrcm] with ⟨%S2, HS, %hS2, #Hsrcm2, #Hkey⟩
    wp_apply wp_mapInsert $$ [$Hcm] as Hcm
    wp_apply wp_mapInsert $$ [$Hsm] as Hsm
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl Hcm Hsm HD HS]
    · iexists (<[key := interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c]> mc1),
        (<[key := true]> ms1), D1, S2
      iframe
      iframe Hdead1 Hsrcm2
      isplitr
      · ipureintro
        intro s' h
        change (<[key := true]> ms1) !! s' = some true
        rw [GMap.lookup_insert_eq_iff]
        rcases hS2 s' h with rfl | h'
        · simp
        · split
          · rfl
          · exact hS1 s' h'
      iapply network.entries_insert $$ [$Hent1]
      iexists c, (cid, true, key)
      iframe Hx
      ipureintro; exact ⟨rfl, rfl, hcD⟩
    wp_apply wp_FromAddrString as %src %hsrc
    wp_apply wp_fork $$ [Hrecv]
    · wp_apply wp_handleConn
          tcp ns v c cid true me la _ key src $$ [$Hrecv]
      · unfold network.tcpCore network.fieldsRO network.addrOkN
        iframe Hrd Hca Hroot Hlock Hreg Hqueue Hip Hconns Hsrcs Hq Hmu
        iexists key
        isplitr
        · ipureintro; exact hsrc
        iright
        iexact Hkey
      itrivial
    wp_for_post
    iframe
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Haerr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    wp_apply wp_slice_literal (V := GoInterface)
      [interface.mkOk go.string #(go!"err"), interface.mkOk (go.GoType.PointerType net.OpError.ty) #pe]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    ihave #HnetD : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
    · solve_pkg_init
    wp_apply network.wp_debug_resErr wp_Debug _ _ _ (some k) $$ [$HnetD $Haerr $Hsl]
    wp_for_post
    iframe

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel



section proofs2
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

theorem network.TCP.Run.wp_proof
    (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (wp_newDecoder : events.newDecoder.spec (GF := GF) (hG := hG))
    (wp_NewNetworkEvent : events.NewNetworkEvent.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_RemoteAddr : net.Conn.RemoteAddr.spec (GF := GF) (hG := hG))
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_FromAddrString : ipv4port.FromAddrString.spec (GF := GF) (hG := hG))
    (wp_String_ptr : ipv4port.IPv4Port.String_ptr.spec (GF := GF) (hG := hG))
    (wp_handleConn : network.TCP.handleConn.spec (GF := GF) (hG := hG)) :
    network.TCP.Run.spec (GF := GF) (hG := hG) := by
  intro tcp γ me
  wp_start as ⟨#Htcp, Htok, #Hprotos⟩
  unfold network.isTCP network.isTCPDef network.tcpCore network.fieldsRO
  icases Htcp with ⟨%ns, %v, %hγ, ⟨⟨#Hip, #Hconns, #Hsrcs, #Hq, #Hmu⟩, #Hroot, #Hlock, #Hreg,
    #Hqueue⟩, #Hcfg, #Hrd, #Hnv⟩
  subst hγ
  ihave %hcfg := ipv4port.ipCfg_str _ _ $$ Hcfg
  obtain ⟨hown, hme⟩ := hcfg
  unfold ipv4port.ipOwn at hown
  wp_auto
  wp_apply wp_String_ptr $$ [$Hip] as -
  rw [hown]
  have hme' : me ∈ VsrWire.addrs := hme
  unfold network.netProtos VsrWire.protos
  ihave #Hpa := (BigSepL.bigSepL_mem (PROP := IProp GF)
    (Φ := fun a' => addrProto (Gg := hG.goose_globalGS) a' (VsrWire.protoOf ns.sys)
      (VsrWire.protoOf ns.sys)) hme') $$ Hprotos
  ihave %Hok := addrTok_ok me $$ [Htok]
  · iexact Htok
  wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp4" net.tcpNet_tcp4 me as %lv %lerr
      (⟨%Hlerr, %l, #Hl, Hlis, #Hla⟩ | ⟨%x, -, #Herr⟩)
  · iframe %Hok
    iapply listen_au $$ Hpa
  · subst Hlerr
    wp_auto
    wp_apply wp_String_ptr $$ [$Hip] as -
    wp_apply wp_slice_literal (V := GoInterface)
      [interface.mkOk go.string #(go!"addr"), interface.mkOk go.string #v.ip'.str']
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply network.wp_debug_wf wp_Debug _ _ _
      (fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil)) $$ [$Hsl]
    wp_apply network.TCP.serve.wp_proof wp_Debug wp_newDecoder wp_NewNetworkEvent wp_Close
        wp_Accept wp_RemoteAddr wp_FromAddrString wp_handleConn tcp ns v lv l me $$ [$Hl $Hlis $Hla $Hpa $Hrd]
    · unfold network.tcpCore network.fieldsRO
      iframe Hip Hconns Hsrcs Hq Hmu Hroot Hlock Hreg Hqueue
    iintro %err -
    wp_auto
    iapply HΦ
    itrivial
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    iapply HΦ
    itrivial

end proofs2

end Perennial.github_com.tangledbytes.go_vsr.pkg

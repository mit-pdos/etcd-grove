/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/AwaitConf.lean (lab master
915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md), onto `Net/`'s `Listen`, `Accept`,
`Read`, `Write` and `Close` (through `SwNetDeps`, as dsv-rabia's `ConfProof.lean`).

kit.go's `awaitConf(addr, ch)`: the configuration protocol's reader, shared by the server nodes
(`serve`) and the client nodes (`newClient`, at their configuration and start ports). Every
connection to a configuration port carries a prefix of a configuration message (the port's dialer
protocol `P`: `conf.dialP` for a server node, `conf.dialPC` for a client node, `conf.startP` for a
client node's start port), so `confLen` bytes read in full are a message `c.encodeC cs` (and `X`,
the protocol's resource: `conf.startP`'s registrations); `decode` accepts it; the first is handed
to the caller over `ch` (a future whose contract is `confMsg γ Ok R`), and every one is
acknowledged (the port's acceptor protocol `Q`). Before the first acknowledgment the node turns
`Pre` and the first message's `X` into the persistent `A` that every acknowledgment needs and `R`,
which the future carries to the caller (a predicted node: its registration,
`client.claimGhost.spec`; the master: nothing; a start port: the registrations). A connection cut
short gives `ReadFull` an error: nothing is decoded, nothing sent.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.KitDeps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Decode
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Perennial.Proof.time

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [SwiftNetPkgState netDistGF] [examples.swiftnet.Assumptions]
variable [net.Assumptions] [io.Assumptions]

set_option goose.wp.extras true in
theorem awaitConf.wp_proof (D : SwNetDeps (hG := hG)) : awaitConf.spec (hG := hG) := by
  intro γ a ch γf P Q Ok Pre A R X hPc hP hQ hclaim
  wp_start as ⟨#Hproto, #Hfut, Hful, HPre⟩
  ihave %Haok := addrTok_ok a $$ [Hproto]
  · iapply addrProto_tok $$ Hproto
  ihave ⟨%ed, #Hed⟩ := kit_ed_init $$ Hpkg
  ihave #Hio : (isPkgInit (PROP := IProp netDistGF) pkg_id.io) $$ []
  · iPkgInit
  wp_auto
  ihave #HnetPk : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · solve_pkg_init
  wp_apply (net.Listen.spec_addrOk D.listen) go!"tcp" net.tcpNet_tcp a as %lv %err Hres
  · (try iframe HnetPk)
    iframe %Haok
    iapply listen_au $$ Hproto
  ihave HI : (∃ (lv err : GoInterface), "l" ∷ l_ptr ↦ lv ∗ "err" ∷ err_ptr ↦ err ∗
      "Hres" ∷ ((⌜err = interface.nil⌝ ∗ ∃ l, ownLis lv l a) ∨
        ∃ i, ⌜err = interface.ok i⌝) : IProp netDistGF) $$ [l err Hres]
  · iexists lv, err
    iframe
    icases Hres with (⟨%He, %l, #Hl, Hlis, #Hla⟩ | ⟨%x, -, #HE⟩)
    · ileft; iframe %He; iexists l; unfold ownLis; iframe Hl Hlis Hla
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      iright; iexists _; ipureintro; rfl
  wp_for HI
  icases Hres with (⟨%Heq, %l, Hl⟩ | ⟨%i, %Hne⟩)
  · subst Heq
    wp_auto
    cleanup_bool_decide
    wp_auto
    unfold ownLis
    icases Hl with ⟨#Hli, Hlis, #Hla⟩
    unfold net.isListener
    icases Hli with ⟨%t, %x, %Ht, #Hlt⟩
    subst Ht
    ihave HJ : (∃ fb : Bool, "first" ∷ first_ptr ↦ fb ∗
        "Hlis" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
        "Hful" ∷ (if fb then Fulfill γf (confMsg γ Ok R) ∗ Pre else □ A) : IProp netDistGF)
        $$ [first Hlis Hful HPre]
    · iexists true; simp only [↓reduceIte]; iframe first Hlis; isplitl [Hful] <;> iassumption
    wp_for HJ
    wp_apply (net.Listener.Accept.spec_addrOk D.accept) t l x a
        (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true)
        (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
          connEnd (Gg := hG.goose_globalGS) cn true Q P [] [] ∗
          connFresh (Gg := hG.goose_globalGS) cn true))
        $$ [Hlis]
      as %cv %err (⟨%Herr, %cid, #Hcv, Hlis, Hend, -⟩ | ⟨%kk, Hlis, #Herr⟩)
    · iframe Hlt Hla
      iapply accept_au a P Q _ l true $$ Hproto Hlis
    · subst Herr
      wp_auto_lc 1
      iunfold connEnd at Hend
      icases Hend with ⟨Hsend, Hrecv⟩
      ihave #Hconn := sendTok_connIs cid true _ _ $$ Hsend
      unfold net.isConn
      icases Hcv with ⟨%tc, %la, %ra, %Hct, #Hca⟩
      subst Hct
      ihave Hsl := slice_array (V := w8) b_ptr 9 _ (by decide) $$ b
      ihave HRL := recvTok_L cid true P [] $$ Hrecv
      try wp_auto
      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
        show (W64 9 - W64 0 : w64) = W64 9 from rfl]
      wp_apply rabia.examples.rabianet.wp_connReadFull D.read D.readFullLt tc cid true a la ra ed
          P [] _ _ $$ [$Hio $Hca $Hed $HRL $Hsl]
        as %n %err ⟨%data, %Hd, Hsl, Hrecv⟩
      obtain ⟨-, hdl, herr⟩ := Hd
      by_cases hl9 : data.length = 9
      · ihave ⟨Hrecv, Hp⟩ := recvTokL_proto _ _ _ _ $$ Hrecv
        iapply fupd_wp
        imod (lc_fupd_elim_later (GF := netDistGF) (E := ⊤)) $$ Hlc1 Hp with #Hp
        imodintro
        unfold protoPrefix
        icases Hp with (%Hnil | ⟨%ext, %Hext, #HP⟩)
        · exfalso; simp at Hnil; rw [Hnil] at hl9; simp at hl9
        ihave #HPd : □ P cid data $$ []
        · iapply hPc.pre cid data ext (List.nil_append data ▸ Hext) $$ HP
        ihave ⟨%cf, %cs, #Hcf, HX, %Hcf⟩ := hP cid data hl9 $$ HPd
        obtain ⟨rfl, Hv, Hcs, Hok⟩ := Hcf
        rw [show List.drop (cf.encodeC cs).length (List.replicate 9 (zero_val w8)) = [] by
          rw [hl9]; rfl, List.append_nil]
        rcases err with e | _
        · dsimp only
          wp_auto
          wp_apply wp_closeConn D tc cid true a la ra $$ [] as %_ -
          · iframe #
          wp_for_post
          iframe
          iexists fb
          iframe
        wp_auto
        rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
          show (W64 9 - W64 0 : w64) = W64 9 from rfl]
        wp_apply wp_decode _ (DFrac.own 1) cf cs Hv Hcs $$ [$Hsl] as %sl ⟨Hsl, Hcsl⟩
        rcases fb with _ | _
        · simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hful with #HA
          ihave #HQ : □ Q cid ([] ++ [W8 107]) $$ []
          · imodintro; rw [show ([] : List w8) ++ [W8 107] = [confAck] from rfl]; iapply hQ; iexact HA
          wp_auto
          wp_apply wp_slice_literal (V := w8) (t := go.byte) _
          isplitr
          · ipureintro; rfl
          iintro %ls ⟨Hls, -⟩
          try wp_auto
          wp_apply wp_ack D tc cid a la ra ed Q _ $$ [$Hsend $Hls] as %nw %err' -
          · iframe #
          try wp_auto
          wp_apply wp_closeConn D tc cid true a la ra $$ [] as %_ -
          · iframe #
          wp_for_post
          iframe
          iexists false
          simp only [Bool.false_eq_true, ↓reduceIte]
          iframe
          iexact HA
        · simp only [↓reduceIte]
          icases Hful with ⟨Hful, HPre⟩
          iapply fupd_wp
          imod hclaim $$ Hpkg HPre HX with ⟨#HA, HR⟩
          imodintro
          ihave #HQ : □ Q cid ([] ++ [W8 107]) $$ []
          · imodintro; rw [show ([] : List w8) ++ [W8 107] = [confAck] from rfl]; iapply hQ; iexact HA
          wp_auto
          wp_apply (wp_future_fulfill (t := examples.swiftnet.msg.ty) γf ch
            (⟨goConf cf, sl⟩ : examples.swiftnet.msg)) $$ [Hful Hcsl HR]
          · iframe Hfut
            unfold Fulfilled
            iexists confMsg γ Ok R
            iframe Hful
            unfold confMsg
            iexists cf, cs
            iframe Hcf Hcsl HR
            ipureintro; exact ⟨Hv, Hcs, Hok, rfl⟩
          try wp_auto
          wp_apply wp_slice_literal (V := w8) (t := go.byte) _
          isplitr
          · ipureintro; rfl
          iintro %ls ⟨Hls, -⟩
          try wp_auto
          wp_apply wp_ack D tc cid a la ra ed Q _ $$ [$Hsend $Hls] as %nw %err' -
          · iframe #
          try wp_auto
          wp_apply wp_closeConn D tc cid true a la ra $$ [] as %_ -
          · iframe #
          wp_for_post
          iframe
          iexists false
          simp only [Bool.false_eq_true, ↓reduceIte]
          iframe
          iexact HA
      · obtain ⟨e, rfl⟩ : ∃ e, err = interface.ok e := by
          rcases err with e | _
          · exact ⟨e, rfl⟩
          · exact absurd (herr rfl) (fun h => hl9 (h.trans rfl))
        dsimp only
        wp_auto
        wp_apply wp_closeConn D tc cid true a la ra $$ [] as %_ -
        · iframe #
        wp_for_post
        iframe
        iexists fb
        iframe
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      try wp_auto
      wp_for_post
      iframe
      iexists fb
      iframe
  · subst Hne
    wp_auto
    rw [if_pos (by simp)]
    wp_auto
    wp_apply time.wp_Sleep
    ihave #HnetPk : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
    · solve_pkg_init
    wp_apply (net.Listen.spec_addrOk D.listen) go!"tcp" net.tcpNet_tcp a as %lv' %err' Hres
    · (try iframe HnetPk)
      iframe %Haok
      iapply listen_au $$ Hproto
    wp_for_post
    iframe
    iexists lv', err'
    iframe
    icases Hres with (⟨%He, %l, #Hl, Hlis, #Hla⟩ | ⟨%x, -, #HE⟩)
    · ileft; iframe %He; iexists l; unfold ownLis; iframe Hl Hlis Hla
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne'
      obtain ⟨pe, rfl⟩ := Hne'.2 (by simp)
      iright; iexists _; ipureintro; rfl

end proof

end Perennial.github_com.imdea_software.swiftpaxos

/-
Package `proxy`: `waitForConnections`, the accept routine: Listen (retried) on the proxy's port,
take the listener's state (with the exclusive `netTok γ k`), then accept on the wildcard
`proxyLis k` (`accept_lis_au` of its `lisProto`), read the client's handshake (`ioLt.ReadFull` over
`net.conn_readerOk`), start the connection's reader (`bufio.NewReader`) and dial the client back.
The library specs it calls are parameters (`Proxy/Results` supplies the proofs).
-/
module

public import Dsverify.Proof.raxos.Proxy.NetAcceptLib
public import Dsverify.Proof.raxos.Proxy.NetPrint
public import Spec.bufio.NewReaderOk
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Conn__Read
public import Perennial.Proof.time.Link
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [net.Assumptions] [net.FieldAssumptions]
variable [go.BasicIntoValInj] [_root_.Perennial.io.Assumptions] [errors.Assumptions]
  [fmt.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

/-- `rd_alloc` at the full mask. -/
theorem rd_alloc_top (γ : QNames) (cn : Nat) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ connFresh cn true ={⊤}=∗ rdCtr γ cn 0 :=
  rd_alloc γ ⊤ (by solve_ndisj) cn

theorem waitForConnections_of [hp : hyp.PrintlnHyp GF]
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_ReadFull : raxos.ioLt.ReadFull.spec (GF := GF) (hG := hG))
    (wp_NewReader : EtcdGrove.bufio.NewReader.specOk (GF := GF) (hG := hG))
    (wp_cl : connectionListener.spec (GF := GF) (hG := hG))
    (wp_cc : connectToClient.spec (GF := GF) (hG := hG)) :
    waitForConnections.spec (GF := GF) (hG := hG) := by
  intro γ c' k pr
  wp_start as ⟨#Hsh, Htok⟩
  ihave ⟨#Hf, #Hc, -, -, #Hn⟩ := proxyShared_net $$ Hsh
  unfold sharedNet
  icases Hn with ⟨%rm, %wm, %bm, %cm, %rt, %rp1, %cb0, %BM, %γw, %CM, %RT, #Hsa, #Hrm, #Hninv,
    #Hwm, #Hwmu, #Hbm, #HBM, %HBM21, #Hmus, #Hcm, #HCM, %HCM21, #Hrt, #HRT, %HRT1, #Hrp1⟩
  ihave %Hk : ⌜1 ≤ k ∧ k ≤ 5⌝ $$ [Hf]
  · unfold sharedFacts; icases Hf with ⟨%Hk, -⟩
    ipureintro
    obtain ⟨⟨hn, -⟩, h1, h2⟩ := Hk
    omega
  ihave #Hpp : lisProto (Gg := hG.goose_globalGS) (proxyLis k) (proxyInProto γ k) silentProto $$ [Hf]
  · unfold sharedFacts netProtos
    icases Hf with ⟨-, -, -, ⟨-, -, -, -, #Hps, -⟩, -⟩
    have hk : ([1, 2, 3, 4, 5] : List Nat)[k - 1]? = some k := by
      have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl
    iapply (BigSepL.bigSepL_lookup hk) $$ Hps
  ihave #Hcons : inv consN (consInv γ) $$ [Hf]
  · unfold sharedFacts; icases Hf with ⟨-, #Hc, -⟩; iexact Hc
  ihave #Hnet : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · iPkgInit
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hpoll : isPkgInit (PROP := IProp GF) pkg_id.internal.poll $$ []
  · iPkgInit
  icases (github_com.mit_pdos.etcd_grove.examples.net.wire.ed_of_poll) $$ Hpoll with ⟨%ed, #Hed⟩
  ihave #Hioi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hioi with ⟨-, -, -, -, #HEOFv, #HUEOFv, -⟩
  iunfold errors.newVar at HEOFv
  iunfold errors.newVar at HUEOFv
  icases HEOFv with ⟨%xe, #Heof, -⟩
  icases HUEOFv with ⟨%xu, #Hueof, -⟩
  wp_auto
  have h0 : sint.Z (W64 0) = 0 := rfl
  have h4 : W64 4 - W64 0 = W64 4 := rfl
  rw [h0, go.arrayIndexRef_0, h4]
  ihave Hsl := slice_array b_ptr 4 _ (by decide) $$ b
  rw [show (zero_val (GoArray w8 4)).arr = [W8 0, W8 0, W8 0, W8 0] from rfl]
  wp_for
  rw [show go!"0.0.0.0:" ++ decStr (7606 + k) = proxyLis k from rfl]
  wp_apply wp_Listen go!"tcp" net.tcpNet_tcp (proxyLis k) as %li %err Hres
  · isplitr
    · ipureintro; exact proxyLis_listenOk k Hk
    iapply listen_lis_au $$ Hpp
  icases Hres with (⟨%Herr, %l, #Hli, Hl, #Hon⟩ | ⟨%x, -, #Herr⟩)
  · subst Herr
    imod net_claim γ k pr rm $$ Hninv Htok with Hown
    iunfold netOwn at Hown
    icases Hown with ⟨%lv0, %M, Hlf, Hmap⟩
    wp_auto
    wp_for_post
    iunfold net.isListener at Hli
    icases Hli with ⟨%t, %x, %Ht, #Hlt⟩
    subst Ht
    ihave HI : iprop(∃ (xs : List w8) (M : GMap w64 Loc), slice.mk b_ptr (W64 4) (W64 4) ↦* xs ∗
        ⌜xs.length = 4⌝ ∗ rm ↦$ M ∗
        pr.[Proxy, go!"Listener"] ↦ interface.mkOk (go.GoType.PointerType net.TCPListener.ty) #t ∗
        netLis (extLocalGS netExt (L := hG.goose_localGS)) l (proxyLis k) true) $$ [Hsl Hmap Hlf Hl]
    · iexists _, M; iframe Hsl Hmap Hlf Hl; ipureintro; rfl
    wp_for HI
    icases HI with ⟨Hsl, %Hxs, Hmap, Hlf, Hl⟩
    wp_auto
    wp_apply wp_Accept t l x (proxyLis k)
        (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l (proxyLis k) true)
        (fun _ cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l (proxyLis k) true ∗
          connEnd (Gg := hG.goose_globalGS) cn true silentProto (proxyInProto γ k) [] [] ∗
          connFresh (Gg := hG.goose_globalGS) cn true))
        $$ [Hl]
      as %cv %err (⟨%Herr, %cn, %a, %Ha, #Hcv, Hl, Hend, Hfr⟩ | ⟨%kk, Hl, #Herr⟩)
    · iframe Hlt Hon
      iapply accept_lis_au (proxyLis k) (proxyInProto γ k) silentProto _ l true $$ Hpp Hl
    · subst Herr
      iunfold net.isConn at Hcv
      icases Hcv with ⟨%tc, %la, %ra, %Hcv, #Hconn⟩
      subst Hcv
      iunfold connEnd at Hend
      icases Hend with ⟨Hs, Hr⟩
      ihave #HcIs := sendTok_connIs cn true _ _ $$ Hs
      ihave Hr := recvTok_L cn true _ _ $$ Hr
      imod (rd_alloc_top γ cn) $$ Hcons Hfr with Hrd
      ihave #Hrok := net.conn_readerOk wp_Read tc cn true a la ra _ ed (proxyInProto γ k)
        $$ [$Hio $Hconn $Heof $Hed]
      wp_auto
      rw [show interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #tc =
        GoInterface.ok (net.connIface tc) from rfl]
      wp_apply wp_ReadFull (net.connIface tc) (fun _ m => 0 < m)
          (recvTokL (Gg := hG.goose_globalGS) cn true (proxyInProto γ k)) _ [] _ xs _ _
        $$ [$Hio $Hrok $Heof $Hueof $Hr $Hsl] as %n %err ⟨%data, %Hd, Hsl, Hr, #Hres⟩
      · ipureintro; intro ys hys; omega
      cases err with
      | ok ie =>
        ihave #Hea := readFull_errAny _ _ la ra ed [] data 4 (GoInterface.ok ie) (by intro h; cases h)
          $$ [$Hio $Heof $Hueof]
        · rw [← Hxs]; iexact Hres
        wp_auto
        wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
        iapply wp_slice_literal (V := GoInterface) (t := go.any)
          [interface.mkOk go.string #go!"Connection id reading error:", GoInterface.ok ie]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iintro %lit ⟨Hlit, -⟩
        wp_auto
        ihave #Hpo := printOk_str_err go!"Connection id reading error:" _ $$ Hea
        wp_apply wp_Println_ok _ _ _ $$ [$Hfmt $Hpo $Hlit] as %n' %e' -
        wp_apply wp_Close tc cn true a la ra (fun _ => iprop(True)) $$ [] as %e ⟨%res, -, -⟩
        · iframe Hconn
          imod close_au cn true $$ HcIs with ⟨%st, %dd, Hst, Hdd, Hcl⟩
          imodintro
          iexists st, dd
          iframe Hst Hdd
          iintro %res %st' %d' %Ho Hst Hdd
          imod Hcl $$ %res %st' %d' %Ho Hst Hdd with -
          imodintro; itrivial
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        simp only [List.length_append, List.length_drop]
        omega
      | nil =>
        ihave %hd4 : ⌜data.length = 4⌝ $$ [Hres]
        · iunfold _root_.Perennial.io.readFullRes at Hres
          icases Hres with (%h | ⟨%e, %h, -⟩)
          · ipureintro; rw [h.1, Hxs]
          · exfalso
            obtain ⟨-, hne, h1, h2⟩ := h
            by_cases hc : e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xe ∧ data ≠ []
            · exact absurd (h1 hc) (by intro h; cases h)
            · exact hne (h2 hc).symm
        rw [List.nil_append] at *
        ihave ⟨Hr, #Hpp'⟩ := recvTokL_proto cn true _ _ $$ Hr
        rw [show List.drop data.length xs = [] from
            List.drop_of_length_le (by omega), List.append_nil]
        wp_auto
        iunfold protoPrefix at Hpp'
        icases Hpp' with (%Hnil | ⟨%ext, %Hext, #Hpe⟩)
        · subst Hnil; simp at hd4
        iunfold proxyInProto at Hpe
        icases Hpe with ⟨%cl, %L, %HL, -⟩
        have hcl : cl < 6 := HL.1
        have hdata : data = hs (21 + cl) := hs_of_prefix (21 + cl) data ext _ Hext HL.2.1 hd4
        subst hdata
        ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
        · iPkgInit
        ihave #Hle := encoding.binary.isInit_access $$ Hbin
        icases Hle with ⟨#Hle, -⟩
        wp_method_call
        wp_call
        wp_auto
        wp_method_call
        wp_call
        wp_auto
        rw [hs_client cl hcl]
        wp_apply wp_load_slice_index _ (sint.Z (W64 1)) _ _ (W8 0) (by word) $$ [Hsl] as Hsl
        · iframe Hsl; ipureintro; rfl
        (try wp_auto)
        wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ (W8 (21 + cl)) (by word) $$ [Hsl] as Hsl
        · iframe Hsl; ipureintro; rfl
        (try wp_auto)
        wp_apply wp_load_slice_index _ (sint.Z (W64 1)) _ _ (W8 0) (by word) $$ [Hsl] as Hsl
        · iframe Hsl; ipureintro; rfl
        (try wp_auto)
        rw [hs_decode cl hcl, ← hs_client cl hcl]
        wp_apply wp_NewReader (net.connIface tc) (fun _ m => 0 < m)
            (recvTokL (Gg := hG.goose_globalGS) cn true (proxyInProto γ k)) _ (hs (21 + cl))
          $$ [$Hbufio $Hrok $Hr] as %br Hbr
        · isplitr
          · ipureintro; exact net.connIface_ne_bufioReader tc
          iapply EtcdGrove.bufio.preUpTo_of_pure
          intro r m hm _; exact hm
        rw [peer_w64 cl hcl]
        wp_apply wp_mapInsert $$ [$Hmap] as Hmap
        wp_apply wp_map_lookup1 $$ [$Hmap] as Hmap
        simp only [peer_w64 cl hcl, ↓reduceIte, Option.getD_some]
        wp_apply wp_fork $$ [Hbr Hrd]
        · wp_apply wp_cl γ c' k pr br _ _ _ cn cl $$ [$Hsh $Hbr $Hrd]
          · ipureintro; intro r m hm; exact hm
          itrivial
        wp_apply wp_cc γ c' k pr cl $$ [$Hsh]
        · ipureintro; exact hcl
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro; rfl
    · ihave #Hea := errAny_resErr' $$ Herr
      ihave %Hne := models_lab.errAny_ne_nil $$ [Hea]
      · icases Hea with ⟨-, #Hea⟩; iexact Hea
      cases err with
      | nil => exact absurd rfl Hne
      | ok i =>
      wp_auto
      wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoInterface) (t := go.any)
        [interface.mkOk go.string #go!"TCP accept error:", GoInterface.ok i]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %lit ⟨Hlit, -⟩
      wp_auto
      ihave #Hpo := printOk_str_err go!"TCP accept error:" _ $$ Hea
      wp_apply wp_Println_ok _ _ _ $$ [$Hfmt $Hpo $Hlit] as %n %e -
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro; exact Hxs
  · ihave %Hne := net.resErr_netErr _ _ _ _ _ _ _ $$ Herr
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    wp_apply time.wp_Sleep
    wp_for_post
    iframe

end proofs

end Perennial.raxos

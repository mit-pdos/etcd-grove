/-
Package `proxy`: `waitForConnections`, the accept routine: Listen (retried) on the proxy's port,
take the listener's state, then accept, read the client's handshake, start the connection's
reader and dial the client back.
-/
module

public import Dsverify.Proof.raxos.Proxy.NetAcceptLib
public import Dsverify.Proof.raxos.Proxy.NetPrint

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
 
  [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

/-- `rd_alloc` at the full mask. -/
theorem rd_alloc_top (γ : QNames) (cid : w64) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ NetConn.connFresh cid true ={⊤}=∗ rdCtr γ cid 0 :=
  rd_alloc γ ⊤ (by solve_ndisj) cid

theorem waitForConnections_of (wp_cl : connectionListener.spec (GF := GF) (hG := hG))
    (wp_cc : connectToClient.spec (GF := GF) (hG := hG)) :
    waitForConnections.spec (GF := GF) (hG := hG) := by
  intro γ c' k pr
  wp_start as ⟨#Hsh, Htok, %Hip⟩
  ihave ⟨#Hf, #Hc, -, -, #Hn⟩ := proxyShared_net $$ Hsh
  unfold sharedNet
  icases Hn with ⟨%rm, %wm, %bm, %cm, %rt, %rp1, %cb0, %BM, %γw, %CM, %RT, #Hsa, #Hrm, #Hninv,
    #Hwm, #Hwmu, #Hbm, #HBM, %HBM21, #Hmus, #Hcm, #HCM, %HCM21, #Hrt, #HRT, %HRT1, #Hrp1⟩
  wp_auto
  have h0 : sint.Z (W64 0) = 0 := rfl
  have h4 : W64 4 - W64 0 = W64 4 := rfl
  rw [h0, go.arrayIndexRef_0, h4]
  ihave Hsl := slice_array b_ptr 4 _ (by decide) $$ b
  rw [show (zero_val (GoArray w8 4)).arr = [W8 0, W8 0, W8 0, W8 0] from rfl]
  wp_for
  rw [serverAddr_eq]
  wp_apply net.ListenWild.wp_proof (ipOf k) go!"0.0.0.0" go!"7000" wild_0000 $$ [Htok]
    as %lv %err ⟨Htok, Hres⟩
  · rw [← proxyAddr_eq]; iframe Htok; ipureintro; exact Hip
  rw [← proxyAddr_eq]
  icases Hres with (⟨%l, %lid, %Hlv, #Hlis⟩ | ⟨%i, %Hlv, -⟩)
  · obtain ⟨rfl, rfl⟩ := Hlv
    imod net_claim pr rm (proxyAddr k) $$ Hninv Htok with Hown
    iunfold netOwn at Hown
    icases Hown with ⟨%lv0, %M, Hlf, Hmap⟩
    wp_auto
    wp_for_post
    ihave #Hpp : addrProto (proxyAddr k) (proxyInProto γ k) silentProto $$ [Hf]
    · unfold sharedFacts netProtos
      icases Hf with ⟨%Hk, -, -, ⟨-, -, -, #Hps, -⟩, -⟩
      have hk : ([1, 2, 3, 4, 5] : List Nat)[k - 1]? = some k := by
        obtain ⟨⟨hn, -⟩, h1, h2⟩ := Hk
        have : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl <;> rfl
      iapply (BigSepL.bigSepL_lookup hk) $$ Hps
    ihave HI : iprop(∃ (xs : List w8) (M : GMap w64 Loc), slice.mk b_ptr (W64 4) (W64 4) ↦* xs ∗
        ⌜xs.length = 4⌝ ∗ rm ↦$ M) $$ [Hsl Hmap]
    · iexists _, M; iframe Hsl Hmap; ipureintro; rfl
    wp_for HI
    wp_apply net.TCPListener.Accept.wp_proof l lid (proxyAddr k) (proxyInProto γ k) silentProto
      $$ [$Hlis $Hpp] as %cv %err Hres
    icases HI with ⟨Hsl, %Hxs, Hmap⟩
    iunfold net.newConnResult at Hres
    icases Hres with (⟨%c, %cid, %Hcv, #Hown, ⟨Hs, Hr⟩, Hfr⟩ | ⟨%i, %Hcv, %code, %Hcode, #Herr⟩)
    · obtain ⟨rfl, rfl⟩ := Hcv
      wp_auto
      ihave #Hcons : inv consN (consInv γ) $$ [Hf]
      · unfold sharedFacts; icases Hf with ⟨-, #Hc, -⟩; iexact Hc
      imod (rd_alloc_top γ cid) $$ Hcons Hfr with Hrd
      ihave #Hconn : net.rpc.connIface (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c)
        cid true $$ []
      · unfold net.rpc.connIface; iexists c; iframe Hown; ipureintro; rfl
      ihave #Hnet : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
      · iPkgInit
      ihave #Hrs := bufio.readsOk_conn _ cid true (proxyInProto γ k) $$ [$Hnet $Hconn]
      wp_apply bufio.wp_ReadFull _ (recvTok cid true (proxyInProto γ k)) [] _ xs
        $$ [$Hrs $Hr $Hsl] as %n %err ⟨%data, %Hd, Hsl, Hr, #Herr⟩
      cases err with
      | ok ie =>
        iunfold bufio.errOrNil at Herr
        icases Herr with (%Hn | ⟨#Hea, -⟩)
        · cases Hn
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
        wp_apply wp_Println_ok _ _ _ $$ [$Hpo $Hlit] as %n' -
        wp_apply net.TCPConn.Close.wp_proof c cid true $$ [$Hown] as %e -
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        simp only [List.length_append, List.length_drop]
        omega
      | nil =>
        have hd4 : data.length = 4 := by
          have := Hd.2.2.mp rfl
          omega
        rw [List.nil_append] at *
        ihave ⟨Hr, Hpp⟩ := recvTok_proto $$ Hr
        iunfold protoPrefix at Hpp
        icases Hpp with (%Hnil | ⟨%ext, %Hext, #Hpe⟩)
        · subst Hnil; simp at hd4
        iunfold proxyInProto at Hpe
        icases Hpe with ⟨%cl, %L, %HL, -⟩
        have hcl : cl < 6 := HL.1
        have hdata : data = hs (21 + cl) := hs_of_prefix (21 + cl) data ext _ Hext HL.2.1 hd4
        subst hdata
        rw [show List.drop (hs (21 + cl)).length xs = [] from
            List.drop_of_length_le (by simp [hs]; omega),
          List.append_nil]
        wp_auto
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
        ihave #Hrok := bufio.readerOk_conn _ cid true (proxyInProto γ k) $$ [$Hnet $Hconn]
        wp_apply bufio.wp_NewReader _ (recvTok cid true (proxyInProto γ k)) (hs (21 + cl)) $$ [$Hrok $Hr]
          as %br Hbr
        rw [peer_w64 cl hcl]
        wp_apply wp_mapInsert $$ [$Hmap] as Hmap
        wp_apply wp_map_lookup1 $$ [$Hmap] as Hmap
        simp only [peer_w64 cl hcl, ↓reduceIte, Option.getD_some]
        wp_apply wp_fork $$ [Hbr Hrd]
        · wp_apply wp_cl γ c' k pr br _ cid cl $$ [$Hsh $Hconn $Hbr $Hrd]
          itrivial
        wp_apply wp_cc γ c' k pr cl $$ [$Hsh]
        · ipureintro; exact hcl
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro; rfl
    · obtain ⟨rfl, rfl⟩ := Hcv
      ihave ⟨#Hea, -⟩ := net.rpc.opErr_errAny _ _ _ $$ Herr
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
      wp_apply wp_Println_ok _ _ _ $$ [$Hpo $Hlit] as %n -
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro; exact Hxs
  · obtain ⟨rfl, rfl⟩ := Hlv
    wp_auto
    wp_apply time.wp_Sleep
    wp_for_post
    iframe

end proofs

end Perennial.raxos

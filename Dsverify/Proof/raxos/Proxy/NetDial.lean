/-
Package `proxy`: `connectToClient` (dial the client back, write the handshake, publish the
writer under `clientWritersMutex`).
-/
module

public import Dsverify.Proof.raxos.Proxy.NetWriter
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Dsverify.Proof.raxos.LibDeps

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
variable [_root_.Perennial.bufio.Assumptions] [net.Assumptions]
variable [QpBufioDeps GF] [QpNetDeps GF]

theorem clientInProto_hs (γ : QNames) (cl k : Nat) (hk : k < 2 ^ 16) (cid : Nat) :
    ⊢ clientInProto (GF := GF) γ cl cid (hs k) := by
  unfold clientInProto
  iexists k, []
  isplitr
  · ipureintro
    refine ⟨hk, by simp, by simp⟩
  · iapply BigSepL.bigSepL_nil.2; iempintro

theorem hs_bytes (k : Nat) (hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5) (x0 x1 : w8) :
    ([x0, x1, W8 0, W8 0].set 0 (W8 (uint.Z (W16 (sint.Z (W64 k)))))).set 1
      (W8 (uint.Z (W16 (sint.Z (W64 k)) >>> W64 8))) = hs k := by
  rcases hk with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem connectToClient_proof : connectToClient.spec (GF := GF) (hG := hG) := by
  intro γ c k pr cl
  wp_start as ⟨#Hsh, %hcl⟩
  ihave ⟨#Hf, #Hc, -, -, #Hn⟩ := proxyShared_net $$ Hsh
  unfold sharedNet
  icases Hn with ⟨%rm, %wm, %bm, %cm, %rt, %rp1, %cb0, %BM, %γw, %CM, %RT, #Hsa, #Hrm, #Hninv,
    #Hwm, #Hwmu, #Hbm, #HBM, %HBM21, #Hmus, #Hcm, #HCM, %HCM21, #Hrt, #HRT, %HRT1, #Hrp1⟩
  wp_auto
  have h0 : sint.Z (W64 0) = 0 := rfl
  have h4 : W64 4 - W64 0 = W64 4 := rfl
  rw [h0, go.arrayIndexRef_0, h4]
  ihave Hsl := slice_array b_ptr 4 _ (by decide) $$ b
  ihave #Hproto : addrProto (clientAddr cl) (clientInProto γ cl) silentProto $$ [Hf]
  · unfold sharedFacts netProtos
    icases Hf with ⟨-, -, -, ⟨-, -, #Hp, -⟩, -⟩
    ihave Hp := BigSepL.bigSepL_lookup (Φ := fun _ c => addrProto (GF := GF) (clientAddr c)
      (clientInProto γ c) silentProto) (show (List.range 6)[cl]? = some cl by simp [hcl]) $$ Hp
    iexact Hp
  ihave HI : iprop(∃ x0 x1 : w8, slice.mk b_ptr (W64 4) (W64 4) ↦* [x0, x1, W8 0, W8 0]) $$ [Hsl]
  · iexists W8 0, W8 0
    rw [show (zero_val (GoArray w8 4)).arr = [W8 0, W8 0, W8 0, W8 0] from rfl]
    iexact Hsl
  wp_for HI
  wp_apply wp_map_lookup1 $$ [HCM] as -
  · iexact HCM
  rw [peer_w64 cl hcl, HCM21 cl hcl]
  simp only [Option.getD_some]
  ihave %Hok2 := addrTok_ok (clientAddr cl) $$ [Hproto]
  · iapply addrProto_tok $$ Hproto
  wp_apply QpNetDeps.dial go!"tcp" net.tcpNet_tcp (clientAddr cl) iprop(True)
      (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false (clientInProto γ cl) silentProto [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cn false)) $$ []
    as %cv %err (⟨%Herr, %cn, #Hc2, ⟨Hend, -⟩⟩ | ⟨-, %x, -, #Herr⟩)
  · isplitr
    · ipureintro; exact Hok2
    isplit
    · itrivial
    · iapply dial_au (clientAddr cl) (clientInProto γ cl) silentProto $$ Hproto
  · subst Herr
    iunfold connEnd at Hend
    icases Hend with ⟨Hs, -⟩
    ihave #Hconn := sendTok_connIs cn false _ _ $$ Hs
    iunfold net.isConn at Hc2
    icases Hc2 with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    wp_auto
    irename HI => Hsl
    unfold sharedConsts
    icases Hc with ⟨#Hname, -⟩
    ihave #Hbin : isPkgInit (PROP := IProp GF) pkg_id.encoding.binary $$ []
    · iPkgInit
    ihave #Hle := encoding.binary.isInit_access $$ Hbin
    icases Hle with ⟨#Hle, -⟩
    wp_auto
    wp_method_call
    wp_call
    wp_auto
    wp_method_call
    wp_call
    wp_auto
    wp_apply wp_load_slice_index _ (sint.Z (W64 1)) [x0, x1, W8 0, W8 0] _ x1 (by word) $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; rfl
    wp_apply wp_store_slice_index _ (sint.Z (W64 0)) _ _ $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro; simp
    (try wp_auto)
    wp_apply wp_store_slice_index _ _ _ _ $$ [Hsl] as Hsl
    · iframe Hsl; ipureintro
      simp
    ihave %Hk : ⌜k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5⌝ $$ [Hf]
    · unfold sharedFacts; icases Hf with ⟨%Hk, -⟩; ipureintro
      obtain ⟨⟨hn, -⟩, h1, h2⟩ := Hk; omega
    rw [hs_bytes k Hk]
    ihave #Hhs := clientInProto_hs γ cl k (by omega) cn
    ihave #Hpoll : isPkgInit (PROP := IProp GF) pkg_id.internal.poll $$ []
    · iPkgInit
    ihave ⟨%ed, #Hed⟩ := github_com.mit_pdos.etcd_grove.examples.net.wire.ed_of_poll $$ Hpoll
    wp_apply QpNetDeps.connWrite t cn false (clientAddr cl) la ra _ (hs k) (DFrac.own 1) ed
        (writeP cn false (clientInProto γ cl) []) $$ [Hsl Hs]
      as %n %err ⟨%w, %res, Hs, Hsl, %Hw, #HE⟩
    · iframe Hca Hsl Hed
      isplitl [Hs]
      · iapply writeP_init $$ Hs
      · iapply write_acc cn false (clientInProto γ cl) [] (hs k)
        simp only [List.nil_append]; iexact Hhs
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
    obtain ⟨hw, -, hnone, -⟩ := Hw
    unfold writeP
    cases res with
    | some ke =>
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      wp_auto
      wp_apply QpNetDeps.connClose t cn false (clientAddr cl) la ra (fun _ => iprop(True)) $$ []
        as %e -
      · iframe Hca
        imod close_au cn false $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
        imodintro
        iexists st, dd
        iframe Hst Hdd
        iintro %res %st' %d' %Hd' Hst Hdd
        imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
        imodintro
        itrivial
      wp_for_post
      iframe
      iexists _, _
      unfold hs
      iexact Hsl
    | none =>
      have herr := Hne.1 rfl
      subst herr
      have hw' : w = hs k := hnone rfl
      subst hw'
      simp only [List.nil_append]
      wp_auto
      wp_apply sync.Mutex.wp_Lock $$ [$Hwmu] as ⟨Hlocked, HR⟩
      ihave #Hwok := net.conn_streamWriterOk QpNetDeps.connWrite t cn false (clientAddr cl) la ra ed
        (clientInProto γ cl) (clientInProto_prefixClosed γ cl) $$ [$Hca $Hed]
      ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
      · iPkgInit
      rw [show interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t = GoInterface.ok (net.connIface t)
        from rfl]
      wp_apply QpBufioDeps.newWriter (net.connIface t) (sendTok cn false (clientInProto γ cl))
          (clientInProto γ cl cn) (net.connWriteE la ra ed) (hs k) $$ [Hs] as %w Hw
      · iframe Hbufio Hwok Hs Hhs
        ipureintro; exact net.connIface_ne_bufioWriter t
      imod inv_alloc wN ⊤ iprop(wSlot γ k (cOf (W64 (21 + cl))) w ∨
          ghostMapElem (γw (W64 (21 + cl))) w DFrac.discard ())
        $$ [Hw] with #Hwinv
      · inext; ileft
        rw [cOf_peer cl hcl]
        unfold wSlot
        iexists _, cn, _, hs k, [], GoInterface.nil
        iframe Hw
        iright
        iexists []
        isplitr
        · ipureintro; simp [ansStream]
        · iapply BigSepL.bigSepL_nil.2; iempintro
      unfold writersR
      icases HR with ⟨%W, Hwmap, Hpubs⟩
      rw [peer_w64 cl hcl]
      wp_apply wp_mapInsert $$ [$Hwmap] as Hwmap
      obtain ⟨mu, Hmu⟩ := Option.isSome_iff_exists.mp (HBM21 cl hcl)
      wp_apply sync.Mutex.wp_Unlock $$ [$Hwmu $Hlocked Hwmap Hpubs]
      · iexists _
        iframe Hwmap
        iapply BigSepM.bigSepM_insert_elim $$ [] Hpubs
        unfold wPub
        iexists mu
        iframe Hwinv
        ipureintro; exact Hmu
      wp_for_post
      wp_end
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe

end proofs

end Perennial.raxos

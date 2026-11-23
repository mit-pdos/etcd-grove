/-
Package `proxy`: `connectToClient` (dial the client back, write the handshake, publish the
writer under `clientWritersMutex`).
-/
module

public import Dsverify.Proof.raxos.Proxy.NetWriter

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

theorem clientInProto_hs (γ : QNames) (cl k : Nat) (hk : k < 2 ^ 16) (cid : w64) :
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
    icases Hf with ⟨-, -, -, ⟨-, #Hp, -⟩, -⟩
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
  wp_apply net.Dial.wp_proof (clientAddr cl) (clientInProto γ cl) silentProto $$ [$Hproto] as %cv %err Hres
  iunfold net.newConnResult at Hres
  icases Hres with (⟨%c, %cid, %Hcv, #Hown, ⟨Hs, Hr⟩, Hfr⟩ | ⟨%i, %Herr0, Herr⟩)
  · obtain ⟨rfl, rfl⟩ := Hcv
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
    ihave #Hhs := clientInProto_hs γ cl k (by omega) cid
    wp_apply net.TCPConn.Write.wp_proof c cid false _ (hs k) (DFrac.own 1) (clientInProto γ cl) []
      $$ [$Hown $Hs Hsl] as %n %err ⟨%k', %code, %Hk', Hsl, Hs, Herr⟩
    · iframe Hsl; imodintro; simp only [List.nil_append]; iexact Hhs
    cases err with
    | ok ie =>
      wp_auto
      wp_apply net.TCPConn.Close.wp_proof c cid false $$ [$Hown] as %e -
      wp_for_post
      iframe
      iexists _, _
      unfold hs
      iexact Hsl
    | nil =>
      have hk' : k' = (hs k).length := Hk'.2.2.2 rfl
      rw [hk', List.take_length, List.nil_append] at *
      wp_auto
      wp_apply sync.Mutex.wp_Lock $$ [$Hwmu] as ⟨Hlocked, HR⟩
      ihave #Hpc := clientInProto_prefixClosed (GF := GF) γ cl cid
      ihave #Hconn : net.rpc.connIface (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c)
        cid false $$ []
      · unfold net.rpc.connIface; iexists c; iframe Hown; ipureintro; rfl
      ihave #Hnet : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
      · iPkgInit
      ihave #Hwok := bufio.writerOk_conn _ cid false (clientInProto γ cl) $$ [$Hnet $Hconn $Hpc]
      wp_apply bufio.wp_NewWriter _ (sendTok cid false (clientInProto γ cl)) (clientInProto γ cl cid) (hs k)
        $$ [$Hwok $Hs] as %w Hw
      · imodintro; iexact Hhs
      imod inv_alloc wN ⊤ iprop(wSlot γ k (cOf (W64 (21 + cl))) w ∨
          ghostMapElem (γw (W64 (21 + cl))) w DFrac.discard ())
        $$ [Hw] with #Hwinv
      · inext; ileft
        rw [cOf_peer cl hcl]
        unfold wSlot
        iexists _, cid, hs k, [], GoInterface.nil
        iframe Hwok Hw
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
  · obtain ⟨rfl, rfl⟩ := Herr0
    wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe

end proofs

end Perennial.raxos

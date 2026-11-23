/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/NetTCP__Connect.lean`, run
`rabia-r1wake-1`, onto `Net/`: `net.Dial.wp_proof` with `dial_au`, `net.Listener.Accept.wp_proof`
with `accept_au` (the listener owned by `accepting`), `net.Conn.Close.wp_proof` with `close_au`
(`wp_closeConn`); readers and writers are `rdOwn`/`wrOwn`; the handshake's facts come from the
protocol one step later.)

`rabia/internal/tcp.(*NetTCP).Connect`: `accepting` and `dialing` in two routines joined by a
local `WaitGroup` (`wp_join_Add2`), then one receive routine per peer (`wp_NetTCP_RecvHandler`)
and one send routine per peer (`wp_NetTCP_SendHandler`).
`accepting` keeps a table entry per peer and counts the distinct peers (N7: a peer's newer
connection replaces its entry, the old one closed, and is not counted twice).
-/
module

public import Dsverify.Proof.rabia.internal.tcp.NetTCP__RecvHandler
public import Dsverify.Proof.rabia.internal.tcp.NetTCP__SendHandler
public import Net.Spec.net.Dial
public import Net.Spec.net.Listener__Accept
public import Net.Proof.net.AtAddr
public import Net.Spec.net.Conn__Close

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia
  rabia.internal.message rabia.internal.config

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.internal.tcp.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions]
variable [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]
variable [msg_sem : rabia.internal.message.Assumptions]

set_option goose.wp.extras true

/-- Closing an end of a connection (`close_au`): nothing to record. -/
theorem wp_closeConn (D : TcpDeps (GF := GF)) (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    {{ net.connAt (GF := GF) t cn s a la ra ∗ connIs (Gg := hG.goose_globalGS) cn }}
      (App (Val #(methods (go.GoType.PointerType net.TCPConn.ty) go!"Close" #t)) (Val #()))
    {{ (err : GoInterface), RET #err; True }} := by
  iintro %Φ ⟨#Hca, #Hconn⟩ HΦ
  iapply D.close t cn s a la ra (fun _ => iprop(True)) $$ []
  · iframe Hca
    imod close_au cn s $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
    imodintro
    iexists st, dd
    iframe Hst Hdd
    iintro %res %st' %d' %Hd' Hst Hdd
    imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
    imodintro
    itrivial
  inext
  iintro %err -
  iapply HΦ
  itrivial

/-- What the dialer leaves for the send routine to server `j`: its channel (ordered, 2 producers)
with the producers' tokens, its writer after the handshake. -/
def dialRes (γ : Names) (cf : RCfg) (k j : Nat) (γo : OrdNames) (ch : GoChan) (bw : Loc) : IProp GF :=
  iprop(∃ (cid : Nat), isOrdChan γo ch 2 (sendP γ cf k j) ∗ ordProd γo 0 0 ∗
    ordProd γo 1 0 ∗ sendSt γ cf k j γo bw cid [0, 0] [])

theorem dial_mono (γ : Names) (cf : RCfg) (k : Nat) (γs : List OrdNames) (chs : List GoChan) (ws : List Loc)
    (i : Nat) (x : GoChan) (y : Loc) (hi : γs.length ≤ i) :
    ([∗list] j ↦ γo ∈ γs, ∃ ch bw, ⌜chs[j]? = some ch ∧ ws[j]? = some bw⌝ ∗
        dialRes (GF := GF) γ cf k j γo ch bw) ⊢
      [∗list] j ↦ γo ∈ γs, ∃ ch bw, ⌜(chs.set i x)[j]? = some ch ∧ (ws.set i y)[j]? = some bw⌝ ∗
        dialRes γ cf k j γo ch bw := by
  apply BigSepL.bigSepL_mono
  intro j γo hj
  have hjl : j < γs.length := (List.getElem?_eq_some_iff.1 hj).1
  have hne : i ≠ j := by omega
  iintro ⟨%ch, %bw, %H, HR⟩
  iexists ch, bw
  iframe HR
  ipureintro
  rw [List.getElem?_set_ne hne, List.getElem?_set_ne hne]
  exact H

theorem netAddr_peer (cf : RCfg) (j : Nat) (hj : j < cf.n) :
    (config.peerStrs cf)[j]? = some (netAddr j) := by
  simp [config.peerStrs, List.getElem?_range hj]

theorem wp_NetTCP_dialing (D : TcpDeps (GF := GF)) (γ : Names) (cf : RCfg) (k : Nat) (hk : k < cf.n) (t : Loc) (scs sns wrs : GoSlice)
    (chs0 : List GoChan) (ss0 ws0 : List Loc) (hl : chs0.length = cf.n ∧ ss0.length = cf.n ∧ ws0.length = cf.n) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗ confRO cf ∗ shared γ ∗
      cfgIs γ.rab cf ∗ t.[NetTCP, go!"Id"] ↦□ (BitVec.ofNat 32 k : w32) ∗
      t.[NetTCP, go!"SendChan"] ↦□ scs ∗ scs ↦* chs0 ∗ t.[NetTCP, go!"SendConn"] ↦□ sns ∗
      sns ↦* ss0 ∗ t.[NetTCP, go!"Writers"] ↦□ wrs ∗ wrs ↦* ws0 }}
    (App (Val (t @!! go.GoType.PointerType NetTCP.ty @!! go!"dialing")) (Val #()))
  {{ RET #(); ∃ (chs : List GoChan) (ss ws : List Loc) (γs : List OrdNames), scs ↦* chs ∗
      sns ↦* ss ∗ wrs ↦* ws ∗ ⌜chs.length = cf.n ∧ ss.length = cf.n ∧ ws.length = cf.n ∧ γs.length = cf.n⌝ ∗
      [∗list] j ↦ γo ∈ γs, ∃ ch bw, ⌜chs[j]? = some ch ∧ ws[j]? = some bw⌝ ∗ dialRes γ cf k j γo ch bw }} := by
  wp_start as ⟨#Hconf, #Hsh, #Hcf, #HId, #HSC, Hscs, #HSN, Hsns, #HW, Hwrs⟩
  ihave #Hconf' := Hconf
  iunfold confRO at Hconf'
  icases Hconf' with ⟨-, %ps, #Hc, #Hps⟩
  ihave Hc2 := Hc
  iStructNamed Hc2
  ihave %Hpl := ownSlice_len _ _ _ $$ Hps
  ihave %Hok := cfgIs_ok γ.rab cf $$ Hcf
  have hn5 : cf.n ≤ 5 := RCfg.n_le_maxS cf Hok
  have hps : ps.len = W64 cf.n := by
    have h1 := Hpl.1; simp only [config.peerStrs, List.length_map, List.length_range] at h1; word
  wp_auto
  simp only [hps, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  wp_auto
  imod monoListLbOwn_nil (GF := GF) (A := MsgV) (γ.net.bcast k) with #Hlb0
  ihave HI : (∃ (i : w64) (chs : List GoChan) (ss ws : List Loc) (γs : List OrdNames),
      "i" ∷ i_ptr ↦ i ∗ "Hscs" ∷ scs ↦* chs ∗ "Hsns" ∷ sns ↦* ss ∗ "Hwrs" ∷ wrs ↦* ws ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ cf.n ∧ γs.length = sint.nat i ∧ chs.length = cf.n ∧
        ss.length = cf.n ∧ ws.length = cf.n⌝ ∗
      "Hds" ∷ ([∗list] j ↦ γo ∈ γs, ∃ ch bw, ⌜chs[j]? = some ch ∧ ws[j]? = some bw⌝ ∗
        dialRes γ cf k j γo ch bw) : IProp GF) $$ [i Hscs Hsns Hwrs]
  · iexists _, chs0, ss0, ws0, []
    iframe
    isplitr
    · ipureintro; refine ⟨by word, by word, rfl, hl⟩
    iapply BigSepL.bigSepL_nil.2; iempintro
  wp_for HI
  wp_if_destruct
  · obtain ⟨hi0, hi3, hγs, hcl, hsl, hwl⟩ := Hi
    have hjn : sint.nat i < cf.n := by word
    have hjm : sint.nat i < maxS := by unfold maxS; omega
    have hix : (sint.Z i).toNat = sint.nat i := rfl
    have hbp : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z ps.len := by rw [hps]; constructor <;> word
    simp only [hbp, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index ps _ _ _ (netAddr (sint.nat i)) hbp.1 $$ [Hps] with -
    · iframe #; ipureintro; exact netAddr_peer cf _ hjn
    ihave #Hproto := shared_netProto γ (sint.nat i) hjm $$ Hsh
    ihave %Haok := addrTok_ok (netAddr (sint.nat i)) $$ [Hproto]
    · iapply addrProto_tok $$ Hproto
    wp_apply D.dial go!"tcp" net.tcpNet_tcp (netAddr (sint.nat i)) iprop(True)
        (fun cn => iprop(connEnd (Gg := hG.goose_globalGS) cn false (netP γ (sint.nat i)) noneP [] [] ∗
          connFresh (Gg := hG.goose_globalGS) cn false))
      as %cv %err (⟨%Herr, %cid, #Hc, Hend, -⟩ | ⟨-, %x, -, #HE⟩)
    · iframe %Haok
      isplit
      · itrivial
      · iapply dial_au _ _ noneP $$ Hproto
    · subst Herr
      wp_auto
      ihave %Hscl := ownSlice_len _ _ _ $$ Hscs
      ihave %Hsnl := ownSlice_len _ _ _ $$ Hsns
      ihave %Hwrl := ownSlice_len _ _ _ $$ Hwrs
      have hb : ∀ (sl : GoSlice) (n : Nat), n = cf.n → n = sint.nat sl.len → 0 ≤ sint.Z sl.len →
          0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := by
        intro sl n h1 h2 h3; subst h1; constructor <;> word
      have hbs := hb scs chs.length hcl Hscl.1 Hscl.2
      have hbn := hb sns ss.length hsl Hsnl.1 Hsnl.2
      have hbw := hb wrs ws.length hwl Hwrl.1 Hwrl.2
      wp_apply (chan.wp_make2 (V := GoSlice) (W64 500000)) as %nch %γn ⟨#Hn, -, Hno⟩
      · ipureintro; decide
      imod start_ord nch 2 (sendP (GF := GF) γ cf k (sint.nat i)) γn $$ Hn [Hno]
        with ⟨%γo, %Hγo, #Hord, Hcons, Hprods⟩
      · iright; iexact Hno
      simp only [hbs, _root_.and_self, ↓reduceIte]
      wp_apply wp_store_slice_index scs _ chs nch $$ [Hscs] as Hscs
      · iframe; ipureintro; rw [hcl]; exact ⟨hbs.1, by word⟩
      simp only [hbn, _root_.and_self, ↓reduceIte]
      wp_apply wp_store_slice_index sns _ ss conn_ptr $$ [Hsns] as Hsns
      · iframe; ipureintro; rw [hsl]; exact ⟨hbn.1, by word⟩
      ipersist conn
      iunfold connEnd at Hend
      icases Hend with ⟨Hsend, Hrecv⟩
      ihave #Hconn := sendTok_connIs cid false _ [] $$ Hsend
      ihave #HP0 := (netP_closed (GF := GF) γ (sint.nat i)).nil cid
      simp only [hbw, _root_.and_self, ↓reduceIte]
      wp_auto
      wp_apply wp_GetReaderWriter D cf conn_ptr cv cid false (netAddr (sint.nat i)) noneP
          (netP γ (sint.nat i)) [] [] (netP_closed γ (sint.nat i))
        $$ [$conn $Hc $Hrecv $Hsend $HP0] as %br %bw ⟨-, Hbw⟩
      · iframe #
      wp_apply wp_store_slice_index wrs _ ws bw $$ [Hwrs] as Hwrs
      · iframe; ipureintro; rw [hwl]; exact ⟨hbw.1, by word⟩
      have hix' : (sint.Z i).toNat = sint.nat i := rfl
      rw [hix']
      simp only [hbw, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index wrs _ (ws.set (sint.nat i) bw) _ bw hbw.1 $$ [Hwrs] with Hwrs
      · iframe; ipureintro; rw [hix']; exact List.getElem?_set_self (by rw [hwl]; exact hjn)
      ipersist «$r0»
      ihave #Hrep : cmdRep (Command.mk (BitVec.ofNat 32 k) 0 0 slice.nil) (hsCmd k) $$ []
      · unfold cmdRep hsCmd
        isplitr
        · ipureintro; exact ⟨rfl, rfl, rfl⟩
        iapply ownSlice_nil
      ihave #HP1 : netP γ (sint.nat i) cid (hsBytes k) $$ []
      · unfold netP
        iright
        iexists cf, k, []
        isplitr
        · iexact Hcf
        isplitr
        · ipureintro; exact ⟨hk, by simp [frames], by simp⟩
        simp only [bcastPart, List.filter_nil]
        isplitr
        · unfold bcastLb; iexact Hlb0
        iapply BigSepL.bigSepL_nil.2; iempintro
      have hlen : (encCmd (hsCmd k)).length < 2 ^ 32 := hsCmd_enc_len k (by omega)
      wp_auto
      wp_apply wp_cmdMarshalWriteFlush D «$r0_ptr» _ (hsCmd k) bw cid false (netP γ (sint.nat i)) [] [] _
        $$ [$«$r0» $Hrep $Hbw] as %e ⟨%sent', %pend', %Hs, Hw⟩
      · isplitr
        · ipureintro; simp [hsCmd]
        imodintro
        iintro -
        simp only [List.nil_append]
        rw [← show hsBytes k = model.frame (encCmd (hsCmd k)) from rfl]
        iexact HP1
      simp only [List.nil_append] at Hs
      rw [← show hsBytes k = model.frame (encCmd (hsCmd k)) from rfl] at Hs
      have Hs2 : sent' ++ pend' <+: hsBytes k ∧ (e = interface.nil → sent' = hsBytes k ∧ pend' = []) := by
        rcases Hs.2 with h | h
        · exact h.2
        · omega
      rcases e with ei | _
      · -- the handshake failed: close, sleep, dial again
        wp_auto
        iunfold net.isConn at Hc
        icases Hc with ⟨%tc, %la, %ra, %Hct, #Hca⟩
        subst Hct
        wp_apply wp_closeConn D tc cid false _ la ra $$ [$Hca $Hconn] as %_ -
        wp_apply time.wp_Sleep
        wp_for_post
        iframe
        iexists _, chs.set (sint.nat i) nch, ss.set (sint.nat i) conn_ptr, ws.set (sint.nat i) bw, γs
        rw [show i - W64 1 + W64 1 = i by word]
        iframe
        isplitr
        · ipureintro; simp [hcl, hsl, hwl]; exact ⟨hi0, hi3, hγs⟩
        iapply dial_mono γ cf k γs chs ws (sint.nat i) nch bw (by omega) $$ Hds
      · obtain ⟨rfl, rfl⟩ := Hs2.2 rfl
        wp_auto
        wp_for_post
        iframe
        iexists _, chs.set (sint.nat i) nch, ss.set (sint.nat i) conn_ptr, ws.set (sint.nat i) bw,
          γs ++ [γo]
        iframe
        isplitr
        · ipureintro
          refine ⟨by word, by word, ?_, by rw [List.length_set, hcl],
            by rw [List.length_set, hsl], by rw [List.length_set, hwl]⟩
          rw [List.length_append, hγs, List.length_singleton]; word
        iapply BigSepL.bigSepL_snoc.2
        isplitl [Hds]
        · iapply dial_mono γ cf k γs chs ws (sint.nat i) nch bw (by omega) $$ Hds
        iexists nch, bw
        isplitr
        · ipureintro
          rw [hγs]
          exact ⟨List.getElem?_set_self (by rw [hcl]; exact hjn),
            List.getElem?_set_self (by rw [hwl]; exact hjn)⟩
        unfold dialRes sendSt
        iexists cid
        rw [hγs]
        rw [show List.range 2 = [0, 1] from rfl, show List.replicate 2 0 = [0, 0] from rfl]
        icases BigSepL.bigSepL_cons.1 $$ Hprods with ⟨Hp0, Hprods⟩
        icases BigSepL.bigSepL_cons.1 $$ Hprods with ⟨Hp1, -⟩
        iframe Hord Hp0 Hp1 Hcons
        simp only [List.map_nil, frames_nil, List.append_nil, bcastPart, List.filter_nil]
        iframe Hw
        isplitr
        · ipureintro; simp
        isplitr
        · unfold bcastLb; iexact Hlb0
        iapply BigSepL.bigSepL_nil.2; iempintro
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      wp_auto
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
      iexists _, chs, ss, ws, γs
      rw [show i - W64 1 + W64 1 = i by word]
      iframe
      ipureintro; exact ⟨hi0, hi3, hγs, hcl, hsl, hwl⟩
  · obtain ⟨hi0, hi3, hγs, hcl, hsl, hwl⟩ := Hi
    iapply HΦ
    iexists chs, ss, ws, γs
    iframe
    ipureintro
    refine ⟨hcl, hsl, hwl, ?_⟩
    rw [hγs]; word

/-- What the acceptor leaves for the receive routine of server `X`'s connection: its reader after
the handshake. -/
def accRes (γ : Names) (k X : Nat) (br : Loc) : IProp GF :=
  iprop(∃ (cid : Nat), rdOwn br cid true (netP γ k) (hsBytes X))

/-- Entry `X` of the acceptor's table (`RecvConn[X]`, `Readers[X]`). -/
def accEntry (γ : Names) (k : Nat) (rcl rl : List Loc) (X : Nat) : IProp GF :=
  iprop(∃ c, ⌜rcl[X]? = some c⌝ ∗ (⌜c = null⌝ ∨
    ((∃ (cv : GoInterface) (cid : Nat) (a : GoString), c ↦□ cv ∗ net.isConn cv cid true a ∗
        connIs (Gg := hG.goose_globalGS) cid) ∗
      ∃ br, ⌜rl[X]? = some br⌝ ∗ accRes γ k X br)))

theorem acc_update (γ : Names) (n : Nat) (k : Nat) (rcl rl : List Loc) (X : Nat) (hX : X < n)
    (c' br' : Loc) :
    ([∗list] j ∈ List.range n, accEntry (GF := GF) γ k rcl rl j) ⊢
      accEntry γ k rcl rl X ∗ (accEntry γ k (rcl.set X c') (rl.set X br') X -∗
        [∗list] j ∈ List.range n, accEntry γ k (rcl.set X c') (rl.set X br') j) := by
  iintro H
  icases BigSepL.bigSepL_lookup_acc_impl (i := X) (x := X) (by rw [List.getElem?_range hX]) $$ H
    with ⟨HX, Hrest⟩
  iframe HX
  iintro HX'
  iapply Hrest $$ %(fun _ j => accEntry γ k (rcl.set X c') (rl.set X br') j) [] HX'
  imodintro
  iintro %j %y %Hy %Hne H
  have hjy : j = y := by
    rw [List.getElem?_range (by have := (List.getElem?_eq_some_iff.1 Hy).1; simpa using this)] at Hy
    exact Option.some.inj Hy
  subst hjy
  unfold accEntry
  icases H with ⟨%c, %Hc, H⟩
  iexists c
  isplitr
  · ipureintro; rw [List.getElem?_set_ne (Ne.symm Hne)]; exact Hc
  icases H with (%Hn | ⟨Hcv, %br, %Hbr, Hr⟩)
  · ileft; ipureintro; exact Hn
  · iright; iframe Hcv; iexists br; iframe Hr
    ipureintro; rw [List.getElem?_set_ne (Ne.symm Hne)]; exact Hbr

theorem acc_init (γ : Names) (n : Nat) (k : Nat) (rl0 : List Loc) :
    ⊢ [∗list] j ∈ List.range n, accEntry (GF := GF) γ k (List.replicate n null) rl0 j := by
  refine BI.Entails.trans (Q := iprop(□ (True : IProp GF))) ?_ (BigSepL.bigSepL_intro ?_)
  · iintro -; imodintro; itrivial
  intro j x hx
  iintro -
  have hj : j < n := by
    have := (List.getElem?_eq_some_iff.1 hx).1; simpa using this
  rw [List.getElem?_range hj] at hx
  cases hx
  unfold accEntry
  iexists null
  isplitr
  · ipureintro; rw [List.getElem?_replicate]; simp [hj]
  ileft; ipureintro; rfl

theorem wp_NetTCP_accepting (D : TcpDeps (GF := GF)) (γ : Names) (cf : RCfg) (k : Nat) (hk : k < cf.n) (t : Loc)
    (li : GoInterface) (lid : w64) (rcs rds : GoSlice) (rl0 : List Loc) (hl : rl0.length = cf.n) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗ confRO cf ∗ shared γ ∗ cfgIs γ.rab cf ∗
      t.[NetTCP, go!"Listener"] ↦□ li ∗ ownListener li lid (netAddr k) ∗
      t.[NetTCP, go!"RecvConn"] ↦□ rcs ∗ rcs ↦* List.replicate cf.n null ∗
      t.[NetTCP, go!"Readers"] ↦□ rds ∗ rds ↦* rl0 }}
    (App (Val (t @!! go.GoType.PointerType NetTCP.ty @!! go!"accepting")) (Val #()))
  {{ RET #(); ∃ (rcl rl : List Loc), rcs ↦* rcl ∗ rds ↦* rl ∗ ⌜rcl.length = cf.n ∧ rl.length = cf.n⌝ ∗
      [∗list] X ∈ List.range cf.n, ∃ br, ⌜rl[X]? = some br⌝ ∗ accRes γ k X br }} := by
  wp_start as ⟨#Hconf, #Hsh, #Hcf, #HL, Hl, #HRC, Hrcs, #HRD, Hrds⟩
  unfold ownListener
  icases Hl with ⟨#Hli, Hlis, #Hla⟩
  unfold net.isListener
  icases Hli with ⟨%tl, %x, %Htl, #Hlt⟩
  subst Htl
  ihave %Hok := cfgIs_ok γ.rab cf $$ Hcf
  have hn5 : cf.n ≤ 5 := RCfg.n_le_maxS cf Hok
  have hNZ : sint.Z (W64 (cf.n : Int)) = cf.n := by word
  ihave #Hproto := shared_netProto γ k (by unfold maxS; omega) $$ Hsh
  ihave #Hconf' := Hconf
  iunfold confRO at Hconf'
  icases Hconf' with ⟨-, %ps, #Hc, -⟩
  ihave Hc2 := Hc
  iStructNamed Hc2
  wp_auto
  ihave HI : (∃ (i : w64) (rcl rl : List Loc), "i" ∷ i_ptr ↦ i ∗ "Hrcs" ∷ rcs ↦* rcl ∗
      "Hrds" ∷ rds ↦* rl ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ cf.n ∧ rcl.length = cf.n ∧ rl.length = cf.n ∧
        rcl.countP (fun c => decide (c ≠ null)) = sint.nat i⌝ ∗
      "Hents" ∷ ([∗list] j ∈ List.range cf.n, accEntry γ k rcl rl j) ∗
      "Hlis" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) lid (netAddr k) true : IProp GF)
      $$ [i Hrcs Hrds Hlis]
  · iexists _, _, rl0
    iframe
    isplitr
    · ipureintro
      refine ⟨by word, by word, by simp, hl, ?_⟩
      rw [List.countP_eq_zero.2 (fun a ha => by simp [List.eq_of_mem_replicate ha])]; rfl
    iapply acc_init
  wp_for HI
  wp_if_destruct
  · obtain ⟨hi0, hi3, hrl, hll, hcnt⟩ := Hi
    have hj3 : sint.Z i < cf.n := by word
    wp_apply (net.Listener.Accept.spec_addrOk D.accept) tl lid x (netAddr k)
        (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) lid (netAddr k) true)
        (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) lid (netAddr k) true ∗
          connEnd (Gg := hG.goose_globalGS) cn true noneP (netP γ k) [] [] ∗
          connFresh (Gg := hG.goose_globalGS) cn true))
        $$ [Hlis]
      as %cv %err (⟨%Herr, %cid, #Hc, Hlis, Hend, -⟩ | ⟨%ek, Hlis, #HE⟩)
    · iframe Hlt Hla
      iapply accept_au (netAddr k) (netP γ k) noneP _ lid true $$ Hproto Hlis
    · subst Herr
      wp_auto
      ipersist conn
      iunfold connEnd at Hend
      icases Hend with ⟨Hsend, Hrecv⟩
      ihave #Hconn := sendTok_connIs cid true _ [] $$ Hsend
      ihave #HP0 := noneP_closed.nil (GF := GF) cid
      wp_apply wp_GetReaderWriter D cf conn_ptr cv cid true (netAddr k) (netP γ k) noneP [] []
          noneP_closed
        $$ [$conn $Hc $Hrecv $Hsend $HP0] as %br %bw ⟨Hbr, -⟩
      · iframe #
      wp_apply (wp_slice_make2 (V := w8) _) as %sl ⟨Hsl, -⟩
      · ipureintro; decide
      ihave %Hsl0 := ownSlice_len _ _ _ $$ Hsl
      have hsl : sint.nat sl.len = 20 := by rw [← Hsl0.1, List.length_replicate]
      ihave #HF := netP_frameIs_hs (GF := GF) γ k cid
      wp_apply (lc := 1) wp_cmdReadUnmarshal D c_ptr br cid true (netP γ k) [] sl _ $$ [$c $Hbr $HF $Hsl]
        as %e ⟨%ds', Hsl, Hres⟩
      icases Hres with (⟨%He, %v, %q, %Hq, Hcmd, #Hrep, Hbr⟩ | ⟨%He, %R', %v, %HR', Hcmd, Hbr⟩)
      · subst He
        have Hq' : (encCmd q).length < 2 ^ 32 := by simp at Hq; omega
        ihave ⟨Hbr, Hpp⟩ := rdOwn_proto br cid true (netP γ k) _ $$ Hbr
        iapply fupd_wp
        imod (lc_fupd_elim_later (GF := GF) (E := ⊤)) $$ Hlc1 Hpp with #Hpp
        imodintro
        ihave %HX := netP_read_hs γ cf k cid q Hq' $$ [$Hcf $Hpp]
        obtain ⟨X, hX, rfl⟩ := HX
        iunfold cmdRep at Hrep
        icases Hrep with ⟨%Hv, -⟩
        obtain ⟨hv1, -, -⟩ := Hv
        wp_auto
        have hi' : sint.Z (W64 (uint.Z (BitVec.ofNat 32 X : w32))) = (X : Int) := by
          word
        have hix : (sint.Z (W64 (uint.Z (BitVec.ofNat 32 X : w32)))).toNat = X := by rw [hi']; simp
        ihave %Hrl := ownSlice_len _ _ _ $$ Hrcs
        ihave %Hdl := ownSlice_len _ _ _ $$ Hrds
        have hb : 0 ≤ sint.Z (W64 (uint.Z (BitVec.ofNat 32 X : w32))) ∧
            sint.Z (W64 (uint.Z (BitVec.ofNat 32 X : w32))) < sint.Z rcs.len := by
          have h1 := Hrl.1; rw [hrl] at h1; rw [hi']; constructor <;> word
        have hbd : 0 ≤ sint.Z (W64 (uint.Z (BitVec.ofNat 32 X : w32))) ∧
            sint.Z (W64 (uint.Z (BitVec.ofNat 32 X : w32))) < sint.Z rds.len := by
          have h1 := Hdl.1; rw [hll] at h1; rw [hi']; constructor <;> word
        icases acc_update γ cf.n k rcl rl X hX conn_ptr br $$ Hents with ⟨HX, Hback⟩
        iunfold accEntry at HX
        icases HX with ⟨%c0, %Hc0, HX⟩
        rw [hv1]
        simp only [hsCmd]
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index rcs _ rcl _ c0 hb.1 $$ [Hrcs] with Hrcs
        · iframe; ipureintro; rw [hix]; exact Hc0
        ihave %Hcn := typedPointsto_not_null $$ conn
        have hXl : X < rcl.length := by rw [hrl]; exact hX
        wp_if_destruct
        · -- no entry yet
          simp only [hb, _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index rcs _ rcl conn_ptr $$ [Hrcs] as Hrcs
          · iframe; ipureintro; exact ⟨hb.1, by have := Hrl.1; have := hb.2; omega⟩
          simp only [hbd, _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index rds _ rl br $$ [Hrds] as Hrds
          · iframe; ipureintro; exact ⟨hbd.1, by have := Hdl.1; have := hbd.2; omega⟩
          rw [hix]
          ihave Hents := Hback $$ [Hbr]
          · unfold accEntry
            iexists conn_ptr
            isplitr
            · ipureintro; exact List.getElem?_set_self (by rw [hrl]; exact hX)
            iright
            isplitr
            · iexists _, cid, _; iframe #
            iexists br
            isplitr
            · ipureintro; exact List.getElem?_set_self (by rw [hll]; exact hX)
            unfold accRes
            iexists cid
            simp only [hsBytes, hsCmd, List.nil_append]
            iexact Hbr
          wp_for_post
          iframe
          iexists _, rcl.set X conn_ptr, rl.set X br
          iframe
          ipureintro
          refine ⟨by word, ?_, by rw [List.length_set, hrl], by rw [List.length_set, hll], ?_⟩
          · word
          · rw [List.countP_set hXl]
            have hc0 : rcl[X] = null := Option.some.inj (by rw [← List.getElem?_eq_getElem hXl]; exact Hc0)
            simp only [hc0, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte,
              Nat.sub_zero, Hcn, not_false_eq_true, _root_.decide_true]
            rw [hcnt]; word
        · -- the peer connected again: replace its entry
          icases HX with (%Hn | ⟨⟨%cv0, %cid0, %a0, #Hcl0, #Hif0, #Hconn0⟩, -⟩)
          · exfalso; exact Hif Hn
          simp only [hb, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index rcs _ rcl _ c0 hb.1 $$ [Hrcs] with Hrcs
          · iframe; ipureintro; rw [hix]; exact Hc0
          iunfold net.isConn at Hif0
          icases Hif0 with ⟨%c1, %la0, %ra0, %Hcv0, #Hca0⟩
          subst Hcv0
          wp_auto
          wp_apply wp_closeConn D c1 cid0 true a0 la0 ra0 $$ [$Hca0 $Hconn0] as %_ -
          simp only [hb, _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index rcs _ rcl conn_ptr $$ [Hrcs] as Hrcs
          · iframe; ipureintro; exact ⟨hb.1, by have := Hrl.1; have := hb.2; omega⟩
          simp only [hbd, _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index rds _ rl br $$ [Hrds] as Hrds
          · iframe; ipureintro; exact ⟨hbd.1, by have := Hdl.1; have := hbd.2; omega⟩
          rw [hix]
          ihave Hents := Hback $$ [Hbr]
          · unfold accEntry
            iexists conn_ptr
            isplitr
            · ipureintro; exact List.getElem?_set_self (by rw [hrl]; exact hX)
            iright
            isplitr
            · iexists _, cid, _; iframe #
            iexists br
            isplitr
            · ipureintro; exact List.getElem?_set_self (by rw [hll]; exact hX)
            unfold accRes
            iexists cid
            simp only [hsBytes, hsCmd, List.nil_append]
            iexact Hbr
          wp_for_post
          iframe
          iexists _, rcl.set X conn_ptr, rl.set X br
          rw [show i - W64 1 + W64 1 = i by word]
          iframe
          ipureintro
          refine ⟨hi0, hi3, by rw [List.length_set, hrl], by rw [List.length_set, hll], ?_⟩
          rw [List.countP_set hXl]
          have hc0 : rcl[X] = c0 := Option.some.inj (by rw [← List.getElem?_eq_getElem hXl]; exact Hc0)
          have hpos : 0 < rcl.countP (fun c => decide (c ≠ null)) :=
            List.countP_pos_iff.2 ⟨c0, List.mem_of_getElem? Hc0, by simpa using Hif⟩
          simp only [hc0, Hif, Hcn, ne_eq, not_false_eq_true, _root_.decide_true, ↓reduceIte]
          simp only [ne_eq] at hcnt hpos
          omega
      · rcases e with ei | _
        · wp_auto
          iunfold net.isConn at Hc
          icases Hc with ⟨%tc, %la, %ra, %Hct, #Hca⟩
          subst Hct
          wp_apply wp_closeConn D tc cid true _ la ra $$ [$Hca $Hconn] as %_ -
          wp_for_post
          iframe
          iexists _, rcl, rl
          rw [show i - W64 1 + W64 1 = i by word]
          iframe
          ipureintro; exact ⟨hi0, hi3, hrl, hll, hcnt⟩
        · exact absurd rfl He
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by cases ek <;> simp)
      wp_auto
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
      iexists _, rcl, rl
      rw [show i - W64 1 + W64 1 = i by word]
      iframe
      ipureintro; exact ⟨hi0, hi3, hrl, hll, hcnt⟩
  · obtain ⟨hi0, hi3, hrl, hll, hcnt⟩ := Hi
    have hi : sint.nat i = cf.n := by word
    have hall : ∀ c ∈ rcl, c ≠ null := by
      have : rcl.countP (fun c => decide (c ≠ null)) = rcl.length := by rw [hcnt, hi, hrl]
      intro c hc
      simpa using (List.countP_eq_length.1 this) c hc
    iapply HΦ
    iexists rcl, rl
    iframe
    isplitr
    · ipureintro; exact ⟨hrl, hll⟩
    iapply (BigSepL.bigSepL_mono ?_) $$ Hents
    intro j x _
    unfold accEntry
    iintro ⟨%c, %Hc, H⟩
    icases H with (%Hn | ⟨-, H⟩)
    · exact absurd Hn (hall c (List.mem_of_getElem? Hc))
    · iexact H

theorem take_at {A : Type} (Φ : Nat → A → IProp GF) (l : List A) (j : Nat) (x : A)
    (h : l[j]? = some x) :
    ([∗list] X ↦ c ∈ l, ⌜X < j⌝ ∨ Φ X c) ⊢ Φ j x ∗ [∗list] X ↦ c ∈ l, ⌜X < j + 1⌝ ∨ Φ X c := by
  iintro H
  icases BigSepL.bigSepL_lookup_acc_impl h $$ H with ⟨Hj, Hrest⟩
  icases Hj with (%Hlt | Hj)
  · omega
  iframe Hj
  iapply Hrest $$ %(fun X c => iprop(⌜X < j + 1⌝ ∨ Φ X c)) []
  · imodintro
    iintro %k %y %_ %_ H
    icases H with (%Hk | H)
    · ileft; ipureintro; omega
    · iright; iexact H
  ileft; ipureintro; omega

/-- The send routine's part of `dialRes` (all but the producers' tokens). -/
def dialRes2 (γ : Names) (cf : RCfg) (k j : Nat) (γo : OrdNames) (ch : GoChan) (bw : Loc) : IProp GF :=
  iprop(∃ (cid : Nat), sendSt γ cf k j γo bw cid [0, 0] [])

theorem dial_split_elem (γ : Names) (cf : RCfg) (k : Nat) (chs : List GoChan) (ws : List Loc) (j : Nat)
    (γo : OrdNames) :
    (∃ ch bw, ⌜chs[j]? = some ch ∧ ws[j]? = some bw⌝ ∗ dialRes (GF := GF) γ cf k j γo ch bw) ⊢
      (ordProd γo 0 0 ∗ ordProd γo 1 0) ∗
      ((∃ ch, ⌜chs[j]? = some ch⌝ ∗ isOrdChan γo ch 2 (sendP γ cf k j)) ∗
       (⌜j < 0⌝ ∨ ∃ ch bw, ⌜chs[j]? = some ch ∧ ws[j]? = some bw⌝ ∗
        isOrdChan γo ch 2 (sendP γ cf k j) ∗ dialRes2 γ cf k j γo ch bw)) := by
  unfold dialRes
  iintro ⟨%ch, %bw, %Hl, %cid, #Hord, Hp0, Hp1, Hst⟩
  iframe Hp0 Hp1
  isplitr
  · iexists ch; iframe Hord; ipureintro; exact Hl.1
  iright
  iexists ch, bw
  iframe Hord
  isplitr
  · ipureintro; exact Hl
  unfold dialRes2
  iexists cid
  iframe

theorem dial_split (γ : Names) (cf : RCfg) (k : Nat) (γs : List OrdNames) (chs : List GoChan) (ws : List Loc) :
    ([∗list] j ↦ γo ∈ γs, ∃ ch bw, ⌜chs[j]? = some ch ∧ ws[j]? = some bw⌝ ∗
        dialRes (GF := GF) γ cf k j γo ch bw) ⊢
      ([∗list] γo ∈ γs, ordProd γo 0 0 ∗ ordProd γo 1 0) ∗
      ([∗list] j ↦ γo ∈ γs, ∃ ch, ⌜chs[j]? = some ch⌝ ∗ isOrdChan γo ch 2 (sendP γ cf k j)) ∗
      ([∗list] j ↦ γo ∈ γs, ⌜j < 0⌝ ∨ ∃ ch bw, ⌜chs[j]? = some ch ∧ ws[j]? = some bw⌝ ∗
        isOrdChan γo ch 2 (sendP γ cf k j) ∗ dialRes2 γ cf k j γo ch bw) := by
  refine (BigSepL.bigSepL_mono (fun {j γo} _ => dial_split_elem γ cf k chs ws j γo)).trans ?_
  refine BigSepL.bigSepL_sep_eqv.1.trans (BI.sep_mono_right BigSepL.bigSepL_sep_eqv.1)

theorem send_view (γ : Names) (cf : RCfg) (k : Nat) (γs : List OrdNames) (chs : List GoChan)
    (hl : chs.length = γs.length) :
    ([∗list] j ↦ γo ∈ γs, ∃ ch, ⌜chs[j]? = some ch⌝ ∗ isOrdChan (GF := GF) γo ch 2 (sendP γ cf k j)) ⊢
      [∗list] j ↦ ch ∈ chs, ∃ γo, ⌜γs[j]? = some γo⌝ ∗ isOrdChan γo ch 2 (sendP γ cf k j) := by
  iintro #H
  iapply (BigSepL.bigSepL_intro (P := iprop(□ ([∗list] j ↦ γo ∈ γs, ∃ ch,
      ⌜chs[j]? = some ch⌝ ∗ isOrdChan (GF := GF) γo ch 2 (sendP γ cf k j)))) ?_) $$ H
  intro j ch hj
  iintro #H
  have hjl : j < γs.length := by rw [← hl]; exact (List.getElem?_eq_some_iff.1 hj).1
  obtain ⟨γo, hγo⟩ : ∃ γo, γs[j]? = some γo := ⟨_, List.getElem?_eq_getElem hjl⟩
  ihave Hj := (BigSepL.bigSepL_lookup hγo) $$ H
  icases Hj with ⟨%ch', %Hch', #Ho⟩
  rw [hj] at Hch'
  cases Hch'
  iexists γo
  iframe Ho
  ipureintro; exact hγo

theorem NetTCP.Connect.wp_proof (D : TcpDeps (GF := GF)) : NetTCP.Connect.spec (GF := GF) := by
  intro γ cf k γl γr t hk
  wp_start as ⟨#Hconf, #Hsh, #Hcf, #Hrecv, Hown, Hlogs⟩
  ihave %Hok := cfgIs_ok γ.rab cf $$ Hcf
  have hn5 : cf.n ≤ 5 := RCfg.n_le_maxS cf Hok
  unfold netTcpOwn
  icases Hown with ⟨%li, %lid, %done, %wg, %scs, %rcs, %sns, %rds, %wrs, %chs0, %ss0, %rs0, %ws0,
    %hk', #HId, #HL, Hl, #HD, #Hdone, #HWg, Hwg, #HSC, Hscs, #HRC, Hrcs, #HSN, Hsns, #HRD, Hrds,
    #HW, Hwrs, %Hlen, Hprods⟩
  obtain ⟨hl1, hl2, hl3, hl4⟩ := Hlen
  wp_auto
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr $$ wg with ⟨%γw, #His, Hctr, Hwaiters⟩
  imod sync.join.init wg_ptr γw $$ [$His $Hctr $Hwaiters] with Had
  ipersist n
  wp_apply wp_join_Add2 wg_ptr
    iprop(∃ (rcl rl : List Loc), rcs ↦* rcl ∗ rds ↦* rl ∗ ⌜rcl.length = cf.n ∧ rl.length = cf.n⌝ ∗
      [∗list] X ∈ List.range cf.n, ∃ br, ⌜rl[X]? = some br⌝ ∗ accRes γ k X br)
    iprop(∃ (chs : List GoChan) (ss ws : List Loc) (γs : List OrdNames), scs ↦* chs ∗
      sns ↦* ss ∗ wrs ↦* ws ∗ ⌜chs.length = cf.n ∧ ss.length = cf.n ∧ ws.length = cf.n ∧ γs.length = cf.n⌝ ∗
      [∗list] j ↦ γo ∈ γs, ∃ ch bw, ⌜chs[j]? = some ch ∧ ws[j]? = some bw⌝ ∗ dialRes γ cf k j γo ch bw)
    $$ [$Had] as ⟨Had, Hd1, Hd2⟩
  wp_apply wp_fork $$ [Hd1 Hrcs Hrds Hl]
  · wp_auto
    wp_apply wp_NetTCP_accepting D γ cf k hk t li lid rcs rds rs0 hl3 $$ [$Hrcs $Hrds $Hl] as HP1
    · iframe #
    wp_apply sync.join.WaitGroup.wp_Done $$ [$Hd1 $HP1]
    itrivial
  wp_apply wp_fork $$ [Hd2 Hscs Hsns Hwrs]
  · wp_auto
    wp_apply wp_NetTCP_dialing D γ cf k hk t scs sns wrs chs0 ss0 ws0 ⟨hl1, hl2, hl4⟩
      $$ [$Hscs $Hsns $Hwrs] as HP2
    · iframe #
    wp_apply sync.join.WaitGroup.wp_Done $$ [$Hd2 $HP2]
    itrivial
  wp_apply (lc := 1) sync.join.WaitGroup.wp_Wait _ _ wg_ptr $$ [$Had] as ⟨HP, -⟩
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HP with HP
  icases HP with ⟨⟨-, %rcl, %rl, Hrcs, Hrds, %Ha, HA⟩, %chs, %ss, %ws, %γs, Hscs, Hsns, Hwrs, %Hd, HD⟩
  ipersist Hrds
  ipersist Hscs
  ipersist Hwrs
  icases dial_split γ cf k γs chs ws $$ HD with ⟨Hprods2, #Hdp, HD⟩
  ihave #Hconf' := Hconf
  iunfold confRO at Hconf'
  icases Hconf' with ⟨-, %ps, #Hc, -⟩
  ihave Hc2 := Hc
  iStructNamed Hc2
  wp_auto
  rw [show (W64 cf.n * W64 2 : w64) = W64 ((2 * cf.n : Nat) : Int) by word]
  wp_apply wp_wgAdd wg (2 * cf.n) (2 * cf.n) (Nat.le_refl _)
    (by have := RCfg.n_pos cf Hok; omega) $$ [$Hwg] as ⟨-, Htoks⟩
  iunfold netTcpRecv at Hrecv
  icases Hrecv with ⟨%rc, #HRC', #Hord⟩
  ihave HR1 := BigSepL.bigSepL_sep_eqv.2 $$ [$HA $Hlogs]
  ihave HR2 := BigSepL.bigSepL_sep_eqv.2 $$ [$HR1 $Hprods]
  ihave HR := (BigSepL.bigSepL_mono (Ψ := fun X x => iprop(⌜X < 0⌝ ∨
      (((∃ br, ⌜rl[x]? = some br⌝ ∗ accRes γ k x br) ∗ (pushAuth γl x [] ∗ rcptAuth γl x ∅)) ∗
        ordProd γr x 0))) (fun _ => BI.or_intro_r)) $$ HR2
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗ "Htoks" ∷ wgToks wg (2 * (cf.n - sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ cf.n⌝ ∗
      "HR" ∷ ([∗list] X ↦ x ∈ List.range cf.n, ⌜X < sint.nat i⌝ ∨
        (((∃ br, ⌜rl[x]? = some br⌝ ∗ accRes γ k x br) ∗ (pushAuth γl x [] ∗ rcptAuth γl x ∅)) ∗
          ordProd γr x 0)) ∗
      "HD" ∷ ([∗list] j ↦ γo ∈ γs, ⌜j < sint.nat i⌝ ∨ ∃ ch bw, ⌜chs[j]? = some ch ∧ ws[j]? = some bw⌝ ∗
        isOrdChan γo ch 2 (sendP γ cf k j) ∗ dialRes2 γ cf k j γo ch bw) : IProp GF) $$ [i Htoks HR HD]
  · iexists _
    rw [show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero]
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · obtain ⟨hi0, hi3⟩ := Hi
    have hX : sint.nat i < cf.n := by word
    have hXZ : sint.Z i = (sint.nat i : Int) := by word
    obtain ⟨γo, hγo⟩ : ∃ γo, γs[sint.nat i]? = some γo :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hd.2.2.2]; exact hX)⟩
    icases take_at _ (List.range cf.n) (sint.nat i) (sint.nat i) (by rw [List.getElem?_range hX]) $$ HR
      with ⟨⟨⟨⟨%br, %Hbr, Hacc⟩, ⟨Hpush, Hrcpt⟩⟩, Hprod⟩, HR⟩
    iunfold accRes at Hacc
    icases Hacc with ⟨%cid, Hrd⟩
    icases take_at _ γs (sint.nat i) γo hγo $$ HD with ⟨⟨%ch, %bw, %Hcw, #Hoc, Hd2⟩, HD⟩
    iunfold dialRes2 at Hd2
    icases Hd2 with ⟨%cid', Hst⟩
    rw [show 2 * (cf.n - sint.nat i) = (2 * (cf.n - (sint.nat i + 1)) + 1) + 1 by omega]
    icases wgToks_split wg _ $$ Htoks with ⟨Htok1, Htoks⟩
    icases wgToks_split wg _ $$ Htoks with ⟨Htok2, Htoks⟩
    wp_apply wp_fork $$ [Hrd Hpush Hrcpt Hprod Htok1]
    · wp_apply wp_NetTCP_RecvHandler D γ cf k γl t i (sint.nat i) hXZ hX rc γr wg rds rl br cid Hbr
        $$ [$Htok1 Hrd Hpush Hrcpt Hprod]
      · iframe #
        unfold recvSt
        simp only [List.map_nil, frames_nil, List.append_nil, List.length_nil]
        iframe
        ipureintro; simp
      itrivial
    wp_apply wp_fork $$ [Hst Htok2]
    · wp_apply wp_NetTCP_SendHandler D γ cf k hk t i (sint.nat i) hXZ hX done wg scs wrs chs ws ch bw
        cid' γo Hcw.1 Hcw.2 $$ [$Htok2 $Hst]
      · iframe #
      itrivial
    wp_for_post
    iframe
    iexists i + W64 1
    rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]
    iframe
    ipureintro; constructor <;> word
  · iapply HΦ
    iexists γs
    iframe Hprods2
    unfold netTcpSend
    iexists scs, chs
    iframe #
    isplitr
    · ipureintro; exact ⟨Hd.1, Hd.2.2.2⟩
    iapply send_view γ cf k γs chs (by rw [Hd.1, Hd.2.2.2]) $$ Hdp
  done

end proof

end Perennial.rabia.internal.tcp

/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/ProxyTCP__Connect.lean`,
run `rabia-r1wake-1`, onto `Net/`'s connections and the revised bufio: `net.Listener.Accept` with
`accept_au` of the proxy address's protocols (the listener owned by the accept routine);
`GetReaderWriter` over the accepted end (`proxyQ` allows the empty stream, so the writer is made
before the handshake is read); the handshake's facts through `rdOwn_proto` one step later (a later
credit) and `rdOwn_sentLb`; closes through `close_au` (a table entry keeps its connection's
`connIs`).)

The proof of `rabia/internal/tcp.(*ProxyTCP).Connect`: the accept routine `connect` (accept, read
the client's handshake, register the connection in the table, start its send and receive
routines).
-/
module

public import Dsverify.Proof.rabia.internal.tcp.ProxyTCP__sendLoop
public import Dsverify.Proof.rabia.internal.tcp.ProxyTCP__recvLoop
public import Net.Spec.net.Listener__Accept
public import Net.Proof.net.AtAddr
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

/-- The table with client `c'`'s entry replaced. -/
theorem table_update (γ : Names) (cs : List Loc) (chs : List GoChan) (c' : Nat) (cl : Loc)
    (ch : GoChan) (hc : c' < chs.length) :
    ([∗list] c ↦ x ∈ cs, ∃ y, ⌜chs[c]? = some y⌝ ∗ tableEntry (GF := GF) γ c x y) ∗
      tableEntry γ c' cl ch ⊢
      [∗list] c ↦ x ∈ cs.set c' cl, ∃ y, ⌜(chs.set c' ch)[c]? = some y⌝ ∗ tableEntry γ c x y := by
  refine BI.Entails.trans (Q := iprop(□ (([∗list] c ↦ x ∈ cs, ∃ y, ⌜chs[c]? = some y⌝ ∗
      tableEntry (GF := GF) γ c x y) ∗ tableEntry γ c' cl ch))) ?_ (BigSepL.bigSepL_intro ?_)
  · iintro ⟨#Hold, #Hnew⟩; imodintro; iframe #
  intro k x hx
  iintro #⟨#Hold, #Hnew⟩
  by_cases hk : k = c'
  · subst hk
    have hkl : k < cs.length := by
      rcases List.getElem?_eq_some_iff.1 hx with ⟨h, -⟩; simpa using h
    rw [List.getElem?_set_self hkl] at hx
    cases hx
    iexists ch
    isplitr
    · ipureintro; exact List.getElem?_set_self hc
    iexact Hnew
  · rw [List.getElem?_set_ne (Ne.symm hk)] at hx
    ihave Hk := (BigSepL.bigSepL_lookup hx) $$ Hold
    icases Hk with ⟨%y, %hy, #Hy⟩
    iexists y
    isplitr
    · ipureintro; rw [List.getElem?_set_ne (Ne.symm hk)]; exact hy
    iexact Hy

theorem inv_alloc_list (N : Nat → Namespace) (Φ Ψ : Nat → IProp GF) (l : List Nat) :
    ([∗list] c ∈ l, Φ c) ⊢ |={⊤}=> [∗list] c ∈ l, inv (N c) iprop(Φ c ∨ Ψ c) := by
  induction l with
  | nil => iintro -; imodintro; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons c l ih =>
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hc, Hl⟩
    imod inv_alloc (N c) ⊤ iprop(Φ c ∨ Ψ c) $$ [Hc] with #Hi
    · inext; ileft; iexact Hc
    imod ih $$ Hl with Hl
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hi Hl

/-- The receipts' invariants, allocated. -/
theorem rcpt_alloc (γ : Names) (k : Nat) (γl : SrvNames) (l : List Nat) :
    ([∗list] c ∈ l, [∗list] n ∈ List.range opBudget, pRcpt (GF := GF) γl c n) ⊢
      |={⊤}=> [∗list] c ∈ l, inv (rcptN k c) (rcptBody γ k γl c) :=
  inv_alloc_list (rcptN k) _ _ l

/-- A close's update: nothing to record. -/
theorem close_true (cn : Nat) (s : Bool) :
    connIs (Gg := hG.goose_globalGS) cn ⊢
      |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
        netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d ∗
        ∀ res st' d', ⌜CloseOutcome st d res st' d'⌝ -∗
          netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st' -∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗
            (fun _ : Option NetErr => iprop(True)) res := by
  iintro #Hc
  imod close_au cn s $$ Hc with ⟨%st, %d, Hst, Hd, Hcl⟩
  imodintro
  iexists st, d
  iframe Hst Hd
  iintro %res %st' %d' %Ho Hst Hd
  imod Hcl $$ %res %st' %d' %Ho Hst Hd with -
  imodintro
  itrivial

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics] [package_sem : rabia.internal.tcp.Assumptions]
variable [_root_.Perennial.bufio.Assumptions] [_root_.Perennial.io.Assumptions]
variable [net.Assumptions] [go.BasicIntoValInj]
variable [msg_sem : rabia.internal.message.Assumptions] [sync.Assumptions]

set_option goose.wp.extras true

theorem wp_ProxyTCP_connect (D : TcpDeps (GF := GF)) (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (p : Loc)
    (hk : k < cf.n) (li : GoInterface) (l : w64) (toProxy done : GoChan) (wg : Loc) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.tcp ∗ confRO cf ∗ shared γ ∗ cfgIs γ.rab cf ∗
      proxyTcpRO γ k p ∗
      structFieldRef ProxyTCP go!"Listener" p ↦□ li ∗ ownListener li l (proxyAddr k) ∗
      structFieldRef ProxyTCP go!"RecvChan" p ↦□ toProxy ∗ isChanBag γl.c2p toProxy (c2pP γ cf k γl) ∗
      structFieldRef ProxyTCP go!"Done" p ↦□ done ∗ doneChan done ∗
      structFieldRef ProxyTCP go!"Wg" p ↦□ wg ∗ wgCtr wg (2 * nC) ∗ rcptInvs γ k γl }}
    (App (Val (p @!! go.GoType.PointerType ProxyTCP.ty @!! go!"connect")) (Val #()))
  {{ RET #(); True }} := by
  wp_start as ⟨#Hconf, #Hsh, #Hcf, #Hro, #HL, Hl, #HRC, #Hbag, #HD, #Hdone, #HWg, Hwg, #Hrc⟩
  ihave %Hok := cfgIs_ok γ.rab cf $$ Hcf
  ihave #Hproto := shared_proxyProto γ k (Nat.lt_of_lt_of_le hk (RCfg.n_le_maxS cf Hok)) $$ Hsh
  unfold ownListener
  icases Hl with ⟨#Hli, Hlis, #Hla⟩
  unfold net.isListener
  icases Hli with ⟨%t, %x, %Ht, #Hlt⟩
  subst Ht
  ihave #Hpkgm : (isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message) $$ []
  · iPkgInit
  ihave #Hconf' := Hconf
  iunfold confRO at Hconf'
  icases Hconf' with ⟨-, %ps, #Hc, #Hps⟩
  ihave Hc2 := Hc
  iStructNamed Hc2
  unfold proxyTcpRO
  icases Hro with ⟨%scs, %cns, %rds, %wrs, #HS, #HC, #HR, #HW, #Hlock⟩
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗ "Hwg" ∷ wgCtr wg (2 * (nC - sint.nat i)) ∗
      "Hlis" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) l (proxyAddr k) true ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ nC⌝ : IProp GF) $$ [i Hwg Hlis]
  · iexists _; iframe
    rw [show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero]
    iframe
    ipureintro; unfold nC; constructor <;> word
  wp_for HI
  wp_if_destruct
  · wp_apply (net.Listener.Accept.spec_addrOk D.accept) t l x (proxyAddr k)
        (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l (proxyAddr k) true)
        (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l (proxyAddr k) true ∗
          connEnd (Gg := hG.goose_globalGS) cn true (proxyQ γ k) (proxyP γ k) [] [] ∗
          connFresh (Gg := hG.goose_globalGS) cn true))
        $$ [Hlis]
      as %cv %err (⟨%Herr, %cn, #Hcv, Hlis, Hend, Hfresh⟩ | ⟨%kk, Hlis, #Herr⟩)
    · iframe Hlt Hla
      iapply accept_au (proxyAddr k) (proxyP γ k) (proxyQ γ k) _ l true $$ Hproto Hlis
    · subst Herr
      wp_auto
      ipersist conn
      unfold connEnd
      icases Hend with ⟨Hsend, Hrecv⟩
      ihave #Hcis := sendTok_connIs cn true (proxyQ γ k) [] $$ Hsend
      ihave #HQ0 : proxyQ γ k cn [] $$ []
      · unfold proxyQ; ileft; ipureintro; rfl
      wp_apply wp_GetReaderWriter D cf conn_ptr cv cn true (proxyAddr k) (proxyP γ k) (proxyQ γ k) [] []
          (proxyQ_closed γ k) $$ [$Hrecv $Hsend] as %br %bw ⟨Hbr, Hbw⟩
      · iframe #
      wp_apply (wp_slice_make2 (V := w8) _) as %sl ⟨Hsl, -⟩
      · ipureintro; decide
      ihave %Hsl0 := ownSlice_len _ _ _ $$ Hsl
      have hsl : sint.nat sl.len = 20 := by rw [← Hsl0.1, List.length_replicate]
      ihave #HF := proxyP_frameIs_hs (GF := GF) γ k cn
      wp_apply wp_cmdReadUnmarshal D req_ptr br cn true (proxyP γ k) [] sl _ $$ [$Hpkgm $req $Hbr $HF $Hsl]
        as %e ⟨%ds', Hsl, Hres⟩
      icases Hres with (⟨%He, %v, %q, %Hq, Hcmd, #Hrep, Hbr⟩ | ⟨%He, %R', %v, %HR', Hcmd, Hbr⟩)
      · subst He
        have Hq' : (encCmd q).length < 2 ^ 32 := by simp at Hq; omega
        ihave ⟨Hbr, #Hsent0⟩ := rdOwn_sentLb br cn true (proxyP γ k) _ $$ Hbr
        wp_auto_lc 1
        ihave ⟨Hbr, Hpp⟩ := rdOwn_proto br cn true (proxyP γ k) _ $$ Hbr
        iapply fupd_wp
        imod (lc_fupd_elim_later (GF := GF) (E := ⊤)) $$ Hlc1 Hpp with #Hpp
        imodintro
        ihave ⟨%c', %Hc'⟩ := proxyP_read_hs γ cf k cn q Hq' $$ [$Hcf $Hpp]
        obtain ⟨hc', hck', rfl⟩ := Hc'
        have hsb : sentLb (Gg := hG.goose_globalGS) cn (!true) ([] ++ model.frame (encCmd (hsCmd c'))) ⊢
            sentLb (Gg := hG.goose_globalGS) cn false (hsBytes c') := by
          simp only [Bool.not_true, List.nil_append]; exact .rfl
        ihave #Hsent := hsb $$ Hsent0
        rw [show ([] : List w8) ++ model.frame (encCmd (hsCmd c')) = hsBytes c' from rfl]
        iunfold cmdRep at Hrep
        icases Hrep with ⟨%Hv, -⟩
        obtain ⟨hv1, -, -⟩ := Hv
        rw [hv1]
        wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hinv⟩
        iunfold tableInv at Hinv
        icases Hinv with ⟨%chs, %cs, %rs, %ws, Hscs, Hcns, Hrds, Hwrs, %Hlen, #Hents⟩
        obtain ⟨hl1, hl2, hl3, hl4⟩ := Hlen
        ihave %Hcl := ownSlice_len _ _ _ $$ Hcns
        ihave %Hsl' := ownSlice_len _ _ _ $$ Hscs
        ihave %Hrl := ownSlice_len _ _ _ $$ Hrds
        ihave %Hwl := ownSlice_len _ _ _ $$ Hwrs
        have hcn : c' < 6 := hc'
        have hi : sint.Z (W64 (uint.Z (BitVec.ofNat 32 c' : w32))) = (c' : Int) := by
          word
        have hb : ∀ (sl : GoSlice), 6 = sint.nat sl.len → 0 ≤ sint.Z sl.len →
            (0 ≤ sint.Z (W64 (uint.Z (BitVec.ofNat 32 c' : w32))) ∧
              sint.Z (W64 (uint.Z (BitVec.ofNat 32 c' : w32))) < sint.Z sl.len) := by
          intro sl h2 h3; rw [hi]; constructor <;> word
        have hbc := hb cns (by rw [← Hcl.1, hl2]; rfl) Hcl.2
        have hbs := hb scs (by rw [← Hsl'.1, hl1]; rfl) Hsl'.2
        have hbr := hb rds (by rw [← Hrl.1, hl3]; rfl) Hrl.2
        have hbw := hb wrs (by rw [← Hwl.1, hl4]; rfl) Hwl.2
        list_elem cs c' as cl0
        simp only [hbc, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index cns _ cs _ cl0 hbc.1 $$ [Hcns] with Hcns
        · iframe; ipureintro; rw [hi]; simpa using Hcl0_lookup
        ihave Hent := (BigSepL.bigSepL_lookup (i := c') Hcl0_lookup) $$ Hents
        icases Hent with ⟨%ch0, %Hch0, #Hent⟩
        wp_if_destruct
        rotate_left
        · iunfold tableEntry at Hent
          icases Hent with (%Hn | ⟨⟨%cv0, %cid0, %a0, #Hcl0, #Hif0, #Hcis0⟩, -⟩)
          · exfalso; exact Hif Hn
          simp only [hbc, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index cns _ cs _ cl0 hbc.1 $$ [Hcns] with Hcns
          · iframe; ipureintro; rw [hi]; simpa using Hcl0_lookup
          iunfold net.isConn at Hif0
          icases Hif0 with ⟨%t0, %la0, %ra0, %Hcv0, #Hca0⟩
          subst Hcv0
          wp_auto
          wp_apply D.close t0 cid0 true a0 la0 ra0 (fun _ => iprop(True)) $$ [] as %_ -
          · iframe Hca0; iapply close_true $$ Hcis0
          simp only [hbc, _root_.and_self, ↓reduceIte]
          have hix : (sint.Z (W64 (uint.Z (BitVec.ofNat 32 c' : w32)))).toNat = c' := by rw [hi]; simp
          wp_apply wp_store_slice_index cns _ cs conn_ptr $$ [Hcns] as Hcns
          · iframe; ipureintro; rw [hi, hl2]; unfold nC; omega
          wp_apply (chan.wp_make2 (V := Command) (W64 500000)) as %nch %γn ⟨#Hn, -, Hno⟩
          · ipureintro; decide
          imod start_bag (repP (GF := GF) γ c') (.Buffered []) nch γn (by simp) $$ Hn Hno with #Hnb
          simp only [hbs, _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index scs _ chs nch $$ [Hscs] as Hscs
          · iframe; ipureintro; rw [hi, hl1]; unfold nC; omega
          simp only [hbw, _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index wrs _ ws bw $$ [Hwrs] as Hwrs
          · iframe; ipureintro; rw [hi, hl4]; unfold nC; omega
          simp only [hbr, _root_.and_self, ↓reduceIte]
          wp_apply wp_store_slice_index rds _ rs br $$ [Hrds] as Hrds
          · iframe; ipureintro; rw [hi, hl3]; unfold nC; omega
          rw [hix]
          simp only [hbs, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index scs _ (chs.set c' nch) _ nch hbs.1 $$ [Hscs] with Hscs
          · iframe; ipureintro; rw [hix]; exact List.getElem?_set_self (by rw [hl1]; exact hc')
          ihave #Hent' : tableEntry γ c' conn_ptr nch $$ []
          · unfold tableEntry
            iright
            isplitl
            · iexists _, cn, (proxyAddr k); iframe conn Hcv Hcis
            iexists γn; iexact Hnb
          ihave #Hents' := table_update γ cs chs c' conn_ptr nch (by rw [hl1]; exact hc') $$ [$Hents $Hent']
          wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hscs Hcns Hrds Hwrs]
          · unfold tableInv
            iexists chs.set c' nch, cs.set c' conn_ptr, rs.set c' br, ws.set c' bw
            iframe
            isplitr
            · ipureintro; simp [hl1, hl2, hl3, hl4]
            iexact Hents'
          have hi6 : sint.nat i < nC := by unfold nC at Hi ⊢; word
          wp_apply wp_wgAdd wg (2 * (nC - sint.nat i)) 2 (by omega) (by omega) $$ [$Hwg] as ⟨Hwg, Htoks⟩
          icases wgToks_split wg 1 $$ Htoks with ⟨Htok1, Htoks⟩
          icases wgToks_split wg 0 $$ Htoks with ⟨Htok2, -⟩
          wp_apply wp_fork $$ [Hbw Htok1]
          · wp_apply wp_ProxyTCP_sendLoop D γ k p c' nch γn bw cn done wg hc' $$ [$Hbw $Htok1]
            · iframe #
            itrivial
          ihave #Hrinv : inv (rcptN k c') (rcptBody γ k γl c') $$ []
          · unfold rcptInvs
            iapply (BigSepL.bigSepL_lookup (i := c') (by rw [List.getElem?_range hc'])) $$ Hrc
          wp_apply wp_fork $$ [Hbr Htok2 Hfresh]
          · wp_apply wp_ProxyTCP_recvLoop D γ cf k γl p c' hc' hck' br cn toProxy wg
              $$ [$Hbr $Htok2 $Hfresh]
            · iframe #
            itrivial
          wp_for_post
          iframe
          iexists i + W64 1
          rw [show nC - sint.nat (i + W64 1) = nC - sint.nat i - 1 by unfold nC at hi6 ⊢; word,
            show 2 * (nC - sint.nat i - 1) = 2 * (nC - sint.nat i) - 2 by omega]
          iframe
          ipureintro; unfold nC at hi6 ⊢; constructor <;> word
        simp only [hbc, _root_.and_self, ↓reduceIte]
        have hix : (sint.Z (W64 (uint.Z (BitVec.ofNat 32 c' : w32)))).toNat = c' := by rw [hi]; simp
        wp_apply wp_store_slice_index cns _ cs conn_ptr $$ [Hcns] as Hcns
        · iframe; ipureintro; rw [hi, hl2]; unfold nC; omega
        wp_apply (chan.wp_make2 (V := Command) (W64 500000)) as %nch %γn ⟨#Hn, -, Hno⟩
        · ipureintro; decide
        imod start_bag (repP (GF := GF) γ c') (.Buffered []) nch γn (by simp) $$ Hn Hno with #Hnb
        simp only [hbs, _root_.and_self, ↓reduceIte]
        wp_apply wp_store_slice_index scs _ chs nch $$ [Hscs] as Hscs
        · iframe; ipureintro; rw [hi, hl1]; unfold nC; omega
        simp only [hbw, _root_.and_self, ↓reduceIte]
        wp_apply wp_store_slice_index wrs _ ws bw $$ [Hwrs] as Hwrs
        · iframe; ipureintro; rw [hi, hl4]; unfold nC; omega
        simp only [hbr, _root_.and_self, ↓reduceIte]
        wp_apply wp_store_slice_index rds _ rs br $$ [Hrds] as Hrds
        · iframe; ipureintro; rw [hi, hl3]; unfold nC; omega
        rw [hix]
        simp only [hbs, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index scs _ (chs.set c' nch) _ nch hbs.1 $$ [Hscs] with Hscs
        · iframe; ipureintro; rw [hix]; exact List.getElem?_set_self (by rw [hl1]; exact hc')
        ihave #Hent' : tableEntry γ c' conn_ptr nch $$ []
        · unfold tableEntry
          iright
          isplitl
          · iexists _, cn, (proxyAddr k); iframe conn Hcv Hcis
          iexists γn; iexact Hnb
        ihave #Hents' := table_update γ cs chs c' conn_ptr nch (by rw [hl1]; exact hc') $$ [$Hents $Hent']
        wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked Hscs Hcns Hrds Hwrs]
        · unfold tableInv
          iexists chs.set c' nch, cs.set c' conn_ptr, rs.set c' br, ws.set c' bw
          iframe
          isplitr
          · ipureintro; simp [hl1, hl2, hl3, hl4]
          iexact Hents'
        have hi6 : sint.nat i < nC := by unfold nC at Hi ⊢; word
        wp_apply wp_wgAdd wg (2 * (nC - sint.nat i)) 2 (by omega) (by omega) $$ [$Hwg] as ⟨Hwg, Htoks⟩
        icases wgToks_split wg 1 $$ Htoks with ⟨Htok1, Htoks⟩
        icases wgToks_split wg 0 $$ Htoks with ⟨Htok2, -⟩
        wp_apply wp_fork $$ [Hbw Htok1]
        · wp_apply wp_ProxyTCP_sendLoop D γ k p c' nch γn bw cn done wg hc' $$ [$Hbw $Htok1]
          · iframe #
          itrivial
        ihave #Hrinv : inv (rcptN k c') (rcptBody γ k γl c') $$ []
        · unfold rcptInvs
          iapply (BigSepL.bigSepL_lookup (i := c') (by rw [List.getElem?_range hc'])) $$ Hrc
        wp_apply wp_fork $$ [Hbr Htok2 Hfresh]
        · wp_apply wp_ProxyTCP_recvLoop D γ cf k γl p c' hc' hck' br cn toProxy wg
            $$ [$Hbr $Htok2 $Hfresh]
          · iframe #
          itrivial
        wp_for_post
        iframe
        iexists i + W64 1
        rw [show nC - sint.nat (i + W64 1) = nC - sint.nat i - 1 by unfold nC at hi6 ⊢; word,
          show 2 * (nC - sint.nat i - 1) = 2 * (nC - sint.nat i) - 2 by omega]
        iframe
        ipureintro; unfold nC at hi6 ⊢; constructor <;> word
      · rcases e with ei | _
        · unfold net.isConn
          icases Hcv with ⟨%tc, %lac, %rac, %Hcvc, #Hcac⟩
          subst Hcvc
          wp_auto
          wp_apply D.close tc cn true (proxyAddr k) lac rac (fun _ => iprop(True))
            $$ [] as %_ -
          · iframe Hcac; iapply close_true $$ Hcis
          wp_for_post
          iframe
          iexists _
          rw [show i - W64 1 + W64 1 = i by word]
          iframe
          ipureintro; exact Hi
        · exact absurd rfl He
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      wp_auto
      wp_for_post
      iapply HΦ
      itrivial
  · iapply HΦ
    itrivial

theorem ProxyTCP.Connect.wp_proof (D : TcpDeps (GF := GF)) : ProxyTCP.Connect.spec (GF := GF) := by
  intro γ cf k γl p
  wp_start as ⟨#Hconf, #Hsh, #Hcf, #Hro, Hown⟩
  unfold proxyTcpOwn
  icases Hown with ⟨%li, %l, %toProxy, %done, %wg, %hk, #HL, Hl, #HRC, #Hbag, #HD, #Hdone,
    #HWg, Hwg, Hrcpts⟩
  imod rcpt_alloc γ k γl _ $$ Hrcpts with #Hrc
  wp_auto
  wp_apply wp_fork $$ [Hwg Hl p]
  · wp_auto
    wp_apply wp_ProxyTCP_connect D γ cf k γl p hk li l toProxy done wg $$ [$Hwg $Hl]
    · iframe #
      unfold rcptInvs; iexact Hrc
    itrivial
  wp_end

end proof

end Perennial.rabia.internal.tcp

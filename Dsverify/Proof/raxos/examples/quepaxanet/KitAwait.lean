/-
`awaitConf(addr, ch)` (`kit.go`), run by every client and server machine at its configuration
address: it listens (retrying), and answers every connection that writes a configuration with an
acknowledgment; the first configuration goes on `ch`. Over the address's protocols
(`addrProto a (confInProto γ) ackProto`, from the shared facts): what a dialer writes is the
configuration the orchestrator chose (`confIs γ c`), so the channel's contract is `confP γ`. The
library specs it calls are parameters (the kit's `Results` supplies the proofs).
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.KitConf
public import Dsverify.Proof.raxos.Proxy.NetAcceptLib
public import Net.Proof.net.AtAddr
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Proof.time.Link
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open raxos raxos.pure

/-- Node `n`'s configuration address (`1 ≤ n ≤ 11`) carries the configuration protocols. -/
theorem confProto_of_shared [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
    [GoGlobalContext] {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]
    [NetProtoGS] [qv : hyp.QpVocab GF] (γ : QNames) (n : Nat) (hn : 1 ≤ n ∧ n ≤ 11) :
    sharedRes (GF := GF) γ ⊢ addrProto (portAddr (7640 + n)) (confInProto γ) ackProto := by
  unfold sharedRes netProtos
  iintro ⟨-, -, ⟨-, -, -, #Hcc, -, #Hcs, -⟩, -⟩
  by_cases h : n ≤ 6
  · have hm : n - 1 ∈ List.range 6 := by simp; omega
    have he : cconfAddr (n - 1) = portAddr (7640 + n) := by
      rw [cconfAddr_eq]; congr 2; omega
    rw [← he]
    iapply (BigSepL.bigSepL_mem (Φ := fun c : Nat => addrProto (cconfAddr c)
      (confInProto (GF := GF) γ) ackProto) hm)
    iexact Hcc
  · have hm : n - 6 ∈ ([1, 2, 3, 4, 5] : List Nat) := by simp; omega
    have he : confAddr (n - 6) = portAddr (7640 + n) := by
      rw [confAddr_eq]; congr 2; omega
    rw [← he]
    iapply (BigSepL.bigSepL_mem (Φ := fun k : Nat => addrProto (confAddr k)
      (confInProto (GF := GF) γ) ackProto) hm)
    iexact Hcs

section await
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [net.Assumptions] [go.BasicIntoValInj]
variable [_root_.Perennial.io.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

set_option goose.wp.extras true

/-- The contract of the configuration channel: a configuration the orchestrator chose. -/
def confP (γ : QNames) : raxos.examples.quepaxanet.Conf → IProp GF :=
  fun v => iprop(∃ c : QConf, ⌜v = goConf c ∧ c.ok⌝ ∗ confIs γ c)

/-- The first five bytes of a stream the configuration protocol allows are the configuration. -/
theorem conf_of_prefix (c : QConf) (data ext : List w8) (h1 : data <+: ext)
    (h2 : ext <+: encConf c) (hl : data.length = 5) : data = encConf c :=
  List.IsPrefix.eq_of_length (h1.trans h2) (by rw [hl]; rfl)

/-- **`awaitConf(a, ch)`** at a configuration address `a` (it never returns: any postcondition). -/
theorem wp_awaitConf_of
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_ReadFull : raxos.ioLt.ReadFull.spec (GF := GF) (hG := hG))
    (γ : QNames) (a : GoString) (ch : Loc) (γc : ChanNames) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ addrProto a (confInProto γ) ackProto ∗
        isChanBag γc ch (confP γ) }}
      (App (App (Val (@! raxos.examples.quepaxanet.awaitConf)) (Val #a)) (Val #ch))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hpr, #Hch⟩
  ihave %Hok := addrTok_ok a $$ [Hpr]
  · iapply addrProto_tok $$ Hpr
  ihave #Hnet : isPkgInit (PROP := IProp GF) pkg_id.net $$ []
  · iPkgInit
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
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
  have wp_L := net.Listen.spec_addrOk wp_Listen
  wp_auto
  wp_apply wp_L go!"tcp" net.tcpNet_tcp a as %li %err Hres
  · isplitr
    · ipureintro; exact Hok
    iapply listen_au $$ Hpr
  ihave HLs : (∃ (lv' err' : GoInterface), "l" ∷ l_ptr ↦ lv' ∗ "err" ∷ err_ptr ↦ err' ∗
      "Hl" ∷ ((⌜err' = interface.nil⌝ ∗ ∃ l, net.isListener lv' l ∗
          netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
          netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a) ∨
        ⌜err' ≠ interface.nil⌝) : IProp GF) $$ [l err Hres]
  · iexists li, err
    iframe l err
    icases Hres with (H | ⟨%x, -, #Herr⟩)
    · ileft; iexact H
    · iright
      ihave %Hne := net.resErr_netErr _ _ _ _ _ _ _ $$ Herr
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      ipureintro; simp
  wp_for HLs
  icases Hl with (⟨%He, %lv, #Hli, Hl, #Hla⟩ | %Hne)
  · subst He
    wp_auto
    rw [if_neg (by
        intro h
        have h' := of_decide_eq_true h
        exact absurd (go.IntoValInj.intoVal_inj (V := Bool) h') (by decide)),
      if_pos (by simp)]
    iunfold net.isListener at Hli
    icases Hli with ⟨%t, %x, %Ht, #Hlt⟩
    subst Ht
    wp_auto
    have wp_A := net.Listener.Accept.spec_addrOk wp_Accept
    ihave HI : (∃ fb : Bool, "first" ∷ first_ptr ↦ fb ∗
        "Hl" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) lv a true : IProp GF) $$ [first Hl]
    · iexists true; iframe
    wp_for HI
    wp_apply wp_A t lv x a
        (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) lv a true)
        (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) lv a true ∗
          connEnd (Gg := hG.goose_globalGS) cn true ackProto (confInProto γ) [] [] ∗
          connFresh (Gg := hG.goose_globalGS) cn true))
        $$ [Hl]
      as %cv %err (⟨%Herr, %cn, #Hcv, Hl, Hend, -⟩ | ⟨%kk, Hl, #Herr⟩)
    · iframe Hlt Hla
      iapply accept_au a (confInProto γ) ackProto _ lv true $$ Hpr Hl
    · subst Herr
      iunfold net.isConn at Hcv
      icases Hcv with ⟨%tc, %la, %ra, %Hcv, #Hconn⟩
      subst Hcv
      iunfold connEnd at Hend
      icases Hend with ⟨Hs, Hr⟩
      ihave #HcIs := sendTok_connIs cn true _ _ $$ Hs
      ihave Hr := recvTok_L cn true _ _ $$ Hr
      ihave #Hrok := net.conn_readerOk wp_Read tc cn true a la ra _ ed (confInProto γ)
        $$ [$Hio $Hconn $Heof $Hed]
      wp_auto
      have h0 : sint.Z (W64 0) = 0 := rfl
      rw [h0, go.arrayIndexRef_0, show W64 5 - W64 0 = W64 5 from rfl]
      ihave Hsl := slice_array b_ptr 5 _ (by decide) $$ b
      rw [show (zero_val (GoArray w8 5)).arr = [W8 0, W8 0, W8 0, W8 0, W8 0] from rfl]
      rw [show interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #tc =
        GoInterface.ok (net.connIface tc) from rfl]
      wp_apply wp_ReadFull (net.connIface tc) (fun _ m => 0 < m)
          (recvTokL (Gg := hG.goose_globalGS) cn true (confInProto γ)) _ [] _ _ _ _
        $$ [$Hio $Hrok $Heof $Hueof $Hr $Hsl] as %n %err ⟨%data, %Hd, Hsl, Hr, #Hres⟩
      · ipureintro; intro ys hys; omega
      cases err with
      | ok ie =>
        wp_auto
        wp_apply wp_Close tc cn true a la ra (fun _ => iprop(True)) $$ [] as %e -
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
        iexists fb
        iframe
      | nil =>
        ihave %hd5 : ⌜data.length = 5⌝ $$ [Hres]
        · iunfold _root_.Perennial.io.readFullRes at Hres
          icases Hres with (%h | ⟨%e, %h, -⟩)
          · ipureintro; rw [h.1]; rfl
          · exfalso
            obtain ⟨-, hne, h1, h2⟩ := h
            by_cases hc : e = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xe ∧ data ≠ []
            · exact absurd (h1 hc) (by intro h; cases h)
            · exact hne (h2 hc).symm
        rw [List.nil_append] at *
        ihave ⟨Hr, #Hpp'⟩ := recvTokL_proto cn true _ _ $$ Hr
        wp_auto
        iunfold protoPrefix at Hpp'
        icases Hpp' with (%Hnil | ⟨%ext, %Hext, #Hpe⟩)
        · subst Hnil; simp at hd5
        iunfold confInProto at Hpe
        icases Hpe with ⟨%c0, ⟨%hc0, %Hpre⟩, #Hconf⟩
        have hdata : data = encConf c0 := conf_of_prefix c0 data ext Hext Hpre hd5
        subst hdata
        rw [show List.drop (encConf c0).length [W8 0, W8 0, W8 0, W8 0, W8 0] = [] from rfl,
          List.append_nil]
        rw [h0, go.arrayIndexRef_0, show W64 5 - W64 0 = W64 5 from rfl]
        wp_apply wp_decode c0 hc0 _ $$ [Hsl] as Hsl
        · iexact Hsl
        ihave #Hack : □ (ackProto (GF := GF) cn ([] ++ [W8 107])) $$ []
        · iintro !>; unfold ackProto; ipureintro; exact List.prefix_refl _
        cases fb
        all_goals wp_auto
        rotate_left
        wp_apply wp_bag_send γc ch (goConf c0) (confP γ) $$ [$Hch]
        · unfold confP; iexists c0; iframe Hconf; ipureintro; exact ⟨rfl, hc0⟩
        all_goals
          wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
          iapply wp_slice_literal (V := w8) (t := go.byte) [W8 107]
          wp_auto
          isplitl []
          · ipureintro; rfl
          iintro %asl ⟨Hasl, -⟩
          (try wp_auto)
          wp_apply wp_Write tc cn true a la ra _ [W8 107] (DFrac.own 1) ed
              (writeP cn true ackProto []) $$ [Hasl Hs]
            as %nw %errw -
          · iframe Hconn Hasl Hed
            isplitl [Hs]
            · iapply writeP_init $$ Hs
            · iapply write_acc cn true ackProto [] [W8 107] $$ Hack
          (try wp_auto)
          wp_apply wp_Close tc cn true a la ra (fun _ => iprop(True)) $$ [] as %e -
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
          iexists _
          iframe
    · ihave %Hne := net.resErr_netErr _ _ _ _ _ _ _ $$ Herr
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      wp_auto
      wp_for_post
      iframe
      iexists fb
      iframe
  · rcases err' with ie | _
    · simp only
      wp_auto
      rw [ite_eq_left_of_eq_true _ _ (by simp)]
      wp_auto
      wp_apply time.wp_Sleep
      wp_apply wp_L go!"tcp" net.tcpNet_tcp a as %li2 %err2 Hres2
      · isplitr
        · ipureintro; exact Hok
        iapply listen_au $$ Hpr
      wp_for_post
      iframe
      iexists li2, err2
      iframe
      icases Hres2 with (H | ⟨%x, -, #Herr⟩)
      · ileft; iexact H
      · iright
        ihave %Hne := net.resErr_netErr _ _ _ _ _ _ _ $$ Herr
        obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
        ipureintro; simp
    · exact absurd rfl Hne

/-- `registerProto()`: nothing. -/
theorem wp_registerProto :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! raxos.examples.quepaxanet.registerProto)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_end

/-- A new bag channel of capacity 1. -/
theorem wp_make_bag1 {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    {t : go.GoType} [IntoValTyped (GF := GF) V t] (P : V → IProp GF) :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make2 [go.GoType.ChannelType go.ChanDir.sendrecv t]))
        (Val #(W64 1)))
    {{ (ch : Loc), RET #ch; ∃ γc, isChanBag γc ch P }} := by
  iintro %Φ - HΦ
  iapply wp_fupd
  wp_apply (chan.wp_make2 (V := V) (W64 1)) as %ch %γc ⟨#Hch, -, Hoc⟩
  · ipureintro; word
  have Hs : match (if (W64 1) = W64 0 then ChanState.Idle else ChanState.Buffered ([] : List V)) with
      | .Idle | .Buffered [] => True | _ => False := by
    rw [if_neg (by decide)]; trivial
  imod start_bag P _ ch γc Hs $$ Hch Hoc with #Hbag
  imodintro
  iapply HΦ
  iexists γc; iexact Hbag

end await

end raxos.examples.quepaxanet
end Perennial

/-
The proofs of `examples/net/acceptloop`'s functions, over the specs of `net` and `wire`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `handle`: a full read of 1 byte (`wire.read_acc` on the up direction: what it read, the dialer
  wrote), its echo (`server_write_au`, with the connection's token), and the close
  (`wire.close_drop_au`); as echo's `serveConn`.
* `Serve`: `Listen`, then the accept loop (`wire.accept_lis_au`: each accepted connection's
  protocol), which forks a `handle` per connection (`wp_fork`), handing it that connection's
  protocol; the loop keeps only the listener.
* `CallOne id`: the dial (`wire.dial_both_au`, the registration `echo_register`), the write of
  `[id]` (`wire.write_au` on the up direction), the full read of the reply (`wire.read_acc` on the
  down direction), and the check: the reply is a prefix of `[id]` (`client_check`) of length 1, so
  `resp[0] = id`.
* `Call`: two forked `CallOne`s, each with copies of the persistent protocol and plan only (each
  owns the connection it dials, so nothing is shared between them), joined by a wait group:
  Perennial's join idiom (`sync.join`), its `Add(2)` by `wp_Add_many` (`Join.lean`), each
  goroutine's `Done` with `True`, the `Wait` with nothing to collect. The `sync` specs are
  hypotheses, as `net`'s.
* `eof_init`: `io.EOF`'s value, from the package's initialization (the commands' `main`s,
  `cmd/*/Main.lean`, call the bodies with it).
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.Defs
public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import NetTcp.Spec.net.Conn__Read
public import NetTcp.Spec.net.Conn__Write
public import NetTcp.Spec.net.Conn__Close
public import NetTcp.Spec.net.Dial
public import NetTcp.Spec.net.Listen
public import NetTcp.Spec.net.Listener__Accept
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.Join
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Done
public import Perennial.Spec.sync.WaitGroup__Wait
public import Perennial.Proof.io

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap sentAll sentLb rcvdAll)

namespace github_com.mit_pdos.etcd_grove.examples.net.acceptloop

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.acceptloop

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : acceptloop.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- `client_check`, its update under a node's invariants (`Defs.lean`'s are the global ghost
state's, the same up to unfolding). -/
theorem client_check' (γm : GName) (cn : Nat) (γ : ConnG) (W resp : List w8) :
    ⊢ inv echoN (echoState (Gg := hG.goose_globalGS) γm) -∗ connName γm cn γ -∗
      sentAll (γ.dir false) W -∗ sentLb (γ.dir true) resp ={⊤}=∗
      ⌜resp <+: W⌝ ∗ sentAll (γ.dir false) W :=
  client_check γm cn γ W resp

theorem wp_handle
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (c : GoInterface) (cn : Nat) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ net.isConn c cn true srvAddr ∗
        connProto γm cn ∗ globalAddr io.EOF ↦□ eof }}
      (App (Val (@! handle)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn echoInvs connProto
  wp_start as ⟨⟨#HaddrInv, #HechoInv⟩, ⟨%t, %Hct, #Hc⟩, ⟨%γ, Hend, Htok, Hru, #Hlbu, #Hname⟩,
    #Heof⟩
  subst Hct
  ihave #Hup := dir_inv γm cn γ false $$ HechoInv Hname
  ihave #Hdown := dir_inv γm cn γ true $$ HechoInv Hname
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr
      buf _ (wire.readP (γ.dir false) cn true TcpEnd.fresh []) eof $$ [Hbuf Hend Hru]
    as %ok ⟨%got, %bs', HP, Hbuf, %Hlen⟩
  · iframe Hbuf Heof
    isplitr [Hend Hru]
    · unfold net.isConn
      iexists t
      iframe Hc
      ipureintro; rfl
    isplitl [Hend Hru]
    · unfold wire.readP; rw [List.append_nil]
      iframe Hend Hru Hlbu
    iapply wire.read_acc echoN cn true (γ.dir false) TcpEnd.fresh []
    simp only [Bool.not_true]
    iexact Hup
  iunfold wire.readP at HP
  icases HP with ⟨Hend, Hru, #Hlb⟩
  rw [List.nil_append]
  cases ok
  · -- the read failed: close
    wp_auto
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
    · iframe Hc
      iapply wire.close_drop_au echoN cn true (γ.dir true) TcpEnd.fresh $$ Hdown Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · -- echo the request, then close
    (try simp only [↓reduceIte])
    obtain ⟨-, -, Hgot⟩ := Hlen
    have Hgot := Hgot rfl
    subst Hgot
    wp_auto
    wp_apply wp_Write t cn true srvAddr buf got (DFrac.own 1)
        (fun _ _ => iprop(tcpEnd G cn true TcpEnd.fresh)) $$ [Hbuf Hend Htok]
      as %n %err ⟨%k, %okw, Hend, Hbuf, -⟩
    · iframe Hc Hbuf
      iapply server_write_au γm cn γ got got TcpEnd.fresh (List.prefix_refl _) $$ HechoInv Hname
        Htok Hlb Hend
    (try wp_auto)
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
    · iframe Hc
      iapply wire.close_drop_au echoN cn true (γ.dir true) TcpEnd.fresh $$ Hdown Hend
    (try wp_auto)
    iapply HΦ
    itrivial


theorem wp_Serve
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗
        tcpPlan G srvAddr (extLocalGS tcpExt (L := hG.goose_localGS)).host ∗
        globalAddr io.EOF ↦□ eof }}
      (App (Val (@! Serve)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof⟩
  icases echoInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HechoInv⟩
  (try wp_auto)
  wp_apply wp_Listen srvAddr $$ Hplan as %li %err (⟨%Herr, %l, #Hli, Hlis, #Hla⟩ | %Herr)
  · -- listening: the accept loop
    subst Herr
    unfold net.isListener
    icases Hli with ⟨%t, %Ht, #Hlt⟩
    subst Ht
    wp_auto
    ihave HI : ("Hlis" ∷ tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l srvAddr true :
      IProp GF) $$ [Hlis]
    · iexact Hlis
    wp_for HI
    wp_apply wp_Accept t l srvAddr
        (tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l srvAddr true)
        (fun cn => iprop(tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l srvAddr true ∗
          connProto γm cn)) $$ [Hlis]
      as %c %err (⟨%Herr, %cn, #Hc, Hlis, Hproto⟩ | ⟨%Herr, Hlis⟩)
    · iframe Hlt Hla
      iapply wire.accept_lis_au addrN srvAddr (connProto γm) _ l true $$ HaddrInv Hlis
    · -- a connection: its handler, in a goroutine of its own
      subst Herr
      wp_auto
      wp_apply wp_fork $$ [Hproto]
      · wp_apply wp_handle wp_ReadFull wp_Write wp_Close γm c cn eof $$ [Hproto]
        · iframe Hinvs Hc Hproto Heof
        itrivial
      (try wp_auto)
      wp_for_post
      iframe
    · -- a failure: go on
      obtain ⟨pe, rfl⟩ := Herr
      wp_auto
      wp_for_post
      iframe
  · -- not listening: return
    obtain ⟨pe, rfl⟩ := Herr
    wp_auto
    iapply HΦ
    itrivial


theorem wp_CallOne
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (h : GoString) (eof : GoInterface) (id : w8) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ tcpPlan G srvAddr h ∗
        globalAddr io.EOF ↦□ eof }}
      (App (Val (@! CallOne)) (Val #id))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof⟩
  icases echoInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HechoInv⟩
  (try wp_auto)
  wp_apply wp_Dial srvAddr h iprop(True) (fun cn => dialerOwn γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hown⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply wire.dial_both_au addrN srvAddr (connProto γm) (dialerOwn γm) $$ HaddrInv
      iintro %cn #Hat Hd Ha
      iapply echo_register γm cn $$ HechoInv Hd Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %Hct, #Hca⟩
    subst Hct
    unfold dialerOwn
    icases Hown with ⟨%γ, Hend, Hsu, Hrd, #Hlbd, #Hname⟩
    ihave #Hup := dir_inv γm cn γ false $$ HechoInv Hname
    ihave #Hdown := dir_inv γm cn γ true $$ HechoInv Hname
    wp_auto
    wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %req ⟨Hreq, -⟩
    · ipureintro; decide
    (try wp_auto)
    ihave %Hrl := ownSlice_len $$ Hreq
    have Hrl1 : sint.Z req.len = 1 := by
      obtain ⟨h1, h2⟩ := Hrl
      simp only [List.length_replicate] at h1
      word
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z req.len by
      rw [Hrl1]; decide)]
    wp_apply wp_store_slice_index req (sint.Z (W64 0)) _ id $$ [$Hreq] as Hreq
    · ipureintro; decide
    (try wp_auto)
    have Hset : (List.replicate 1 (zero_val w8)).set 0 id = [id] := rfl
    isimp only [Hset] at Hreq
    wp_apply wp_Write t cn false srvAddr req _ (DFrac.own 1)
        (fun k ok => iprop(tcpEnd G cn false TcpEnd.fresh ∗
          sentAll (γ.dir false) ([] ++ [id].take k) ∗
          ⌜∃ d d', WriteOutcome TcpEnd.fresh d [id] k ok d'⌝))
        $$ [Hreq Hend Hsu]
      as %n %err ⟨%k, %okw, ⟨Hend, Hsu, %Hwr⟩, Hreq, %Hn⟩
    · iframe Hca Hreq
      iapply wire.write_au echoN cn false (γ.dir false) TcpEnd.fresh [] [id] $$ Hup Hend Hsu
    obtain ⟨-, Hnil, Herr⟩ := Hn
    cases okw
    · -- the write failed: close and return
      obtain ⟨pe, rfl⟩ := Herr rfl
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply wire.close_drop_au echoN cn false (γ.dir false) TcpEnd.fresh $$ Hup Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    rw [Hnil rfl]
    obtain ⟨d, d', Hwr⟩ := Hwr
    have hk : k = 1 := wire.writeOutcome_ok Hwr
    subst hk
    wp_auto
    wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
    · ipureintro; decide
    (try wp_auto)
    wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false
        srvAddr buf _ (wire.readP (γ.dir true) cn false TcpEnd.fresh []) eof $$ [Hbuf Hend Hrd]
      as %ok ⟨%got, %bs', HP, Hbuf, %Hlen⟩
    · iframe Hbuf Heof
      isplitr [Hend Hrd]
      · unfold net.isConn
        iexists t
        iframe Hca
        ipureintro; rfl
      isplitl [Hend Hrd]
      · unfold wire.readP; rw [List.append_nil]
        iframe Hend Hrd Hlbd
      iapply wire.read_acc echoN cn false (γ.dir true) TcpEnd.fresh []
      simp only [Bool.not_false]
      iexact Hdown
    iunfold wire.readP at HP
    icases HP with ⟨Hend, Hrd, #Hlb⟩
    simp only [List.nil_append]
    cases ok
    · -- the read failed: close
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply wire.close_drop_au echoN cn false (γ.dir false) TcpEnd.fresh $$ Hup Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    · -- the reply is a prefix of `[id]` of its length
      (try simp only [↓reduceIte])
      obtain ⟨hsl, -, Hgot⟩ := Hlen
      have Hgot := Hgot rfl
      subst Hgot
      imod client_check' γm cn γ _ got $$ HechoInv Hname Hsu Hlb with ⟨%Hpre, Hsu⟩
      have hs : got = [id] := by
        simp only [List.take_of_length_le (by simp : List.length [id] ≤ 1)]
          at Hpre
        exact Hpre.eq_of_length (by simpa using hsl)
      subst hs
      wp_auto
      ihave %Hbl := ownSlice_len $$ Hbuf
      have Hbl1 : sint.Z buf.len = 1 := by
        obtain ⟨h1, h2⟩ := Hbl
        simp only [List.length_singleton] at h1
        word
      rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z buf.len by
        rw [Hbl1]; decide)]
      wp_apply wp_load_slice_index buf (sint.Z (W64 0)) [id] (DFrac.own 1) id (by decide)
        $$ [$Hbuf] as Hbuf
      · ipureintro; rfl
      (try wp_auto)
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply wire.close_drop_au echoN cn false (γ.dir false) TcpEnd.fresh $$ Hup Hend
      (try wp_auto)
      iapply HΦ
      itrivial
  · obtain ⟨pe, rfl⟩ := Herr
    wp_auto
    iapply HΦ
    itrivial


theorem wp_Call
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG))
    (wp_Wait : sync.WaitGroup.Wait.spec (GF := GF) (hG := hG))
    (γm : GName) (h : GoString) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ tcpPlan G srvAddr h ∗
        globalAddr io.EOF ↦□ eof }}
      (App (Val (@! Call)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof⟩
  (try wp_auto)
  -- the wait group, and its two goroutines added at once
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr $$ wg with ⟨%γwg, Hwg⟩
  imod sync.join.init wg_ptr γwg $$ Hwg with Hwg
  wp_apply (wp_Add_many wp_Add wg_ptr iprop(True) [iprop(True), iprop(True)] (by simp))
    $$ [Hwg] as ⟨Hwg, Hdones⟩
  · iframe Hwg
  icases BigSepL.bigSepL_cons.1 $$ Hdones with ⟨Hd1, Hdones⟩
  icases BigSepL.bigSepL_cons.1 $$ Hdones with ⟨Hd2, -⟩
  (try wp_auto)
  wp_apply wp_fork $$ [Hd1]
  · (try wp_auto)
    wp_apply wp_CallOne wp_Dial wp_ReadFull wp_Write wp_Close γm h eof (W8 1) $$ []
    · iframe Hinvs Hplan Heof
    (try wp_auto)
    wp_apply (sync.join.WaitGroup.wp_Done_of wp_Done iprop(True) wg_ptr) $$ [Hd1]
    · iframe Hd1
    itrivial
  (try wp_auto)
  wp_apply wp_fork $$ [Hd2]
  · (try wp_auto)
    wp_apply wp_CallOne wp_Dial wp_ReadFull wp_Write wp_Close γm h eof (W8 2) $$ []
    · iframe Hinvs Hplan Heof
    (try wp_auto)
    wp_apply (sync.join.WaitGroup.wp_Done_of wp_Done iprop(True) wg_ptr) $$ [Hd2]
    · iframe Hd2
    itrivial
  (try wp_auto)
  wp_apply (sync.join.WaitGroup.wp_Wait_of wp_Wait _ _ wg_ptr) $$ [Hwg] as -
  · iframe Hwg
  (try wp_auto)
  iapply HΦ
  itrivial


/-- `io.EOF`'s value, from the package's initialization. -/
theorem eof_init :
    isPkgInit (PROP := IProp GF) pkg ⊢ ∃ eof : GoInterface, globalAddr io.EOF ↦□ eof := by
  iintro #Hpkg
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hn := io.eof_of_init $$ Hio
  isimp only [_root_.Perennial.errors.newVar] at Hn
  icases Hn with ⟨%eofl, #Heof, -⟩
  iexists _
  iexact Heof

end proof

end github_com.mit_pdos.etcd_grove.examples.net.acceptloop
end Perennial

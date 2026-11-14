/-
The proofs of `examples/net/echo`'s functions, over the specs of `net` and `wire`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `serveConn`: a full read of 5 bytes (`wire.read_acc` on the up-direction: a prefix of the
  dialer's), its echo (`server_write_au`, with the connection's token), and the close
  (`close_au_drop`).
* `Serve`: `Listen`, then the accept loop (`wire.accept_lis_au`: each accepted connection's protocol).
* `Call`: the dial (`dial_au2`, the deposit `echo_deposit`), the write of `"hello"`
  (`wire.write_au`), the full read of the reply (`wire.read_acc` on the down-direction), and the
  check: the reply is a prefix of `"hello"` (`client_check`) of its length, so `"hello"`.
* `SendJunk`: as `Call`, without the check.
* `Server`, `Client`, `Junk`: the bodies, then `wire.Forever`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.Defs
public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.Forever
public import NetTcp.Spec.net.Conn__Read
public import NetTcp.Spec.net.Conn__Write
public import NetTcp.Spec.net.Conn__Close
public import NetTcp.Spec.net.Dial
public import NetTcp.Spec.net.Listen
public import NetTcp.Spec.net.Listener__Accept
public import Perennial.Proof.io

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap sentAll sentLb rcvdAll)

namespace github_com.mit_pdos.etcd_grove.examples.net.echo

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.echo

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : echo.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- `client_check`, its update under a node's invariants (`Defs.lean`'s are the global ghost
state's, the same up to unfolding). -/
theorem client_check' (γm : GName) (cn : Nat) (γ : EchoNames) (W resp : List w8) :
    ⊢ inv echoN (echoState (GF := GF) γm) -∗ echoName γm cn γ -∗
      sentAll (GF := GF) γ.up W -∗ sentLb (GF := GF) γ.down resp ={⊤}=∗
      ⌜resp <+: W⌝ ∗ sentAll (GF := GF) γ.up W :=
  client_check γm cn γ W resp

theorem wp_serveConn
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (c : GoInterface) (cn : Nat) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ net.isConn c cn true srvAddr ∗
        connProto γm cn ∗ globalAddr io.EOF ↦□ eof }}
      (App (Val (@! serveConn)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn echoInvs connProto
  wp_start as ⟨⟨#HaddrInv, #HechoInv⟩, ⟨%t, %Hct, #Hc⟩, ⟨%γ, #Hname, Hend, Htok, Hr, #Hlb0⟩,
    #Heof⟩
  subst Hct
  ihave #HdU := echo_dirInv_up γm cn γ $$ HechoInv Hname
  ihave #HdD := echo_dirInv_down γm cn γ $$ HechoInv Hname
  ihave #Hacc := wire.read_acc echoN cn true γ.up TcpEnd.fresh [] $$ [HdU]
  · simp only [Bool.not_true]
    iexact HdU
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 5)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr
      buf _ (wire.readP γ.up cn true TcpEnd.fresh []) eof $$ [Hbuf Hend Hr]
    as %ok ⟨%got, %bs', HP, Hbuf, %Hres⟩
  · iframe Hbuf Heof Hacc
    isplitr [Hend Hr]
    · unfold net.isConn
      iexists t
      iframe Hc
      ipureintro; rfl
    unfold wire.readP
    simp only [List.append_nil]
    iframe Hend Hr Hlb0
  unfold wire.readP
  icases HP with ⟨Hend, -, #Hlb⟩
  obtain ⟨-, -, Hok⟩ := Hres
  cases ok
  · -- the read failed: close
    wp_auto
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
    · iframe Hc
      iapply close_au_drop echoN cn true γ.down _ $$ HdD Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · -- echo the request, then close
    obtain rfl := Hok rfl
    wp_auto
    wp_apply wp_Write t cn true srvAddr buf got (DFrac.own 1)
        (fun _ _ => tcpEnd G cn true TcpEnd.fresh) $$ [Hbuf Hend Htok]
      as %n %err ⟨%k, %okw, Hend, Hbuf, -⟩
    · iframe Hc Hbuf
      iapply server_write_au γm cn γ got ([] ++ got) TcpEnd.fresh (by simp) $$ HechoInv Hname
        Htok Hlb Hend
    (try wp_auto)
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
    · iframe Hc
      iapply close_au_drop echoN cn true γ.down _ $$ HdD Hend
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
    · -- a connection: serve it
      subst Herr
      wp_auto
      wp_apply wp_serveConn wp_ReadFull wp_Write wp_Close γm c cn eof $$ [Hproto]
      · iframe Hinvs Hc Hproto Heof
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


theorem wp_Call
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (h : GoString) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ tcpPlan G srvAddr h ∗
        globalAddr io.EOF ↦□ eof }}
      (App (Val (@! Call)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof⟩
  icases echoInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HechoInv⟩
  (try wp_auto)
  wp_apply wp_Dial srvAddr h iprop(True) (fun cn => dialerOwn γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hown⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply dial_au2 addrN srvAddr (connProto γm) (dialerOwn γm) $$ HaddrInv
      iintro %cn #Hat Hd Ha
      iapply echo_deposit γm cn $$ HechoInv Hat Hd Ha
  · subst Herr
    unfold dialerOwn
    icases Hown with ⟨%γ, #Hname, Hend, Hw, Hr, #Hlb0⟩
    unfold net.isConn
    icases Hc with ⟨%t, %Hct, #Hca⟩
    subst Hct
    ihave #HdU := echo_dirInv_up γm cn γ $$ HechoInv Hname
    ihave #HdD := echo_dirInv_down γm cn γ $$ HechoInv Hname
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Write t cn false srvAddr sl _ (DFrac.own 1)
        (fun k ok => iprop(tcpEnd G cn false TcpEnd.fresh ∗
          sentAll γ.up ([] ++ (go!"hello").take k) ∗
          ⌜∃ d d', WriteOutcome TcpEnd.fresh d (go!"hello") k ok d'⌝))
        $$ [Hsl Hend Hw]
      as %n %err ⟨%k, %okw, ⟨Hend, Hw, %Hwr⟩, Hsl, %Hn⟩
    · iframe Hca Hsl
      iapply wire.write_au echoN cn false γ.up TcpEnd.fresh [] _ $$ HdU Hend Hw
    obtain ⟨-, Hnil, Herr⟩ := Hn
    cases okw
    · -- the write failed: close and return
      obtain ⟨pe, rfl⟩ := Herr rfl
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply close_au_drop echoN cn false γ.up _ $$ HdU Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    rw [Hnil rfl]
    obtain ⟨d0, d0', Hwr⟩ := Hwr
    obtain rfl := wire.writeOutcome_ok Hwr
    wp_auto
    wp_apply (wp_slice_make2 (V := w8) (W64 5)) as %buf ⟨Hbuf, -⟩
    · ipureintro; decide
    (try wp_auto)
    ihave #Hacc := wire.read_acc echoN cn false γ.down TcpEnd.fresh [] $$ [HdD]
    · simp only [Bool.not_false]
      iexact HdD
    wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false
        srvAddr buf _ (wire.readP γ.down cn false TcpEnd.fresh []) eof $$ [Hbuf Hend Hr]
      as %ok ⟨%got, %bs', HP, Hbuf, %Hres⟩
    · iframe Hbuf Heof Hacc
      isplitr [Hend Hr]
      · unfold net.isConn
        iexists t
        iframe Hca
        ipureintro; rfl
      unfold wire.readP
      simp only [List.append_nil]
      iframe Hend Hr Hlb0
    unfold wire.readP
    icases HP with ⟨Hend, -, #Hlb⟩
    obtain ⟨Hlen, -, Hok⟩ := Hres
    cases ok
    · -- the read failed: close
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply close_au_drop echoN cn false γ.up _ $$ HdU Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    · -- the reply is a prefix of `"hello"` of its length
      obtain rfl := Hok rfl
      imod client_check' γm cn γ _ ([] ++ got) $$ HechoInv Hname Hw Hlb with ⟨%Hpre, -⟩
      have hs : got = go!"hello" := by
        simp only [List.nil_append, List.take_length] at Hpre
        exact Hpre.eq_of_length (by simpa using Hlen)
      subst hs
      wp_auto
      wp_apply wp_bytes_to_string buf (go!"hello") (DFrac.own 1) $$ Hbuf as Hbuf
      (try wp_auto)
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply close_au_drop echoN cn false γ.up _ $$ HdU Hend
      (try wp_auto)
      iapply HΦ
      itrivial
  · obtain ⟨pe, rfl⟩ := Herr
    wp_auto
    iapply HΦ
    itrivial


theorem wp_SendJunk
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (h : GoString) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ tcpPlan G srvAddr h ∗
        globalAddr io.EOF ↦□ eof }}
      (App (Val (@! SendJunk)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof⟩
  icases echoInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HechoInv⟩
  (try wp_auto)
  wp_apply wp_Dial srvAddr h iprop(True) (fun cn => dialerOwn γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hown⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply dial_au2 addrN srvAddr (connProto γm) (dialerOwn γm) $$ HaddrInv
      iintro %cn #Hat Hd Ha
      iapply echo_deposit γm cn $$ HechoInv Hat Hd Ha
  · subst Herr
    unfold dialerOwn
    icases Hown with ⟨%γ, #Hname, Hend, Hw, Hr, #Hlb0⟩
    unfold net.isConn
    icases Hc with ⟨%t, %Hct, #Hca⟩
    subst Hct
    ihave #HdU := echo_dirInv_up γm cn γ $$ HechoInv Hname
    ihave #HdD := echo_dirInv_down γm cn γ $$ HechoInv Hname
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Write t cn false srvAddr sl _ (DFrac.own 1)
        (fun k ok => iprop(tcpEnd G cn false TcpEnd.fresh ∗
          sentAll γ.up ([] ++ (go!"xxxxxxxxxx").take k) ∗
          ⌜∃ d d', WriteOutcome TcpEnd.fresh d (go!"xxxxxxxxxx") k ok d'⌝))
        $$ [Hsl Hend Hw]
      as %n %err ⟨%k, %okw, ⟨Hend, -, -⟩, Hsl, -⟩
    · iframe Hca Hsl
      iapply wire.write_au echoN cn false γ.up TcpEnd.fresh [] _ $$ HdU Hend Hw
    (try wp_auto)
    wp_apply (wp_slice_make2 (V := w8) (W64 3)) as %buf ⟨Hbuf, -⟩
    · ipureintro; decide
    (try wp_auto)
    ihave #Hacc := wire.read_acc echoN cn false γ.down TcpEnd.fresh [] $$ [HdD]
    · simp only [Bool.not_false]
      iexact HdD
    wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false
        srvAddr buf _ (wire.readP γ.down cn false TcpEnd.fresh []) eof $$ [Hbuf Hend Hr]
      as %ok ⟨%got, %bs', HP, Hbuf, -⟩
    · iframe Hbuf Heof Hacc
      isplitr [Hend Hr]
      · unfold net.isConn
        iexists t
        iframe Hca
        ipureintro; rfl
      unfold wire.readP
      simp only [List.append_nil]
      iframe Hend Hr Hlb0
    unfold wire.readP
    icases HP with ⟨Hend, -, -⟩
    (try wp_auto)
    wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
    · iframe Hca
      iapply close_au_drop echoN cn false γ.up _ $$ HdU Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · obtain ⟨pe, rfl⟩ := Herr
    wp_auto
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

theorem wp_Server
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Forever : wire.Forever.spec (GF := GF) (hG := hG))
    (γm : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗
        tcpPlan G srvAddr (extLocalGS tcpExt (L := hG.goose_localGS)).host }}
      (App (Val (@! Server)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  icases eof_init $$ Hpkg with ⟨%eof, #Heof⟩
  (try wp_auto)
  wp_apply wp_Serve wp_Listen wp_Accept wp_ReadFull wp_Write wp_Close γm eof $$ []
  · iframe Hinvs Hplan Heof
  (try wp_auto)
  wp_apply wp_Forever as ⟨⟩

theorem wp_Client
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Forever : wire.Forever.spec (GF := GF) (hG := hG))
    (γm : GName) (h : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ tcpPlan G srvAddr h }}
      (App (Val (@! Client)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  icases eof_init $$ Hpkg with ⟨%eof, #Heof⟩
  (try wp_auto)
  wp_apply wp_Call wp_Dial wp_ReadFull wp_Write wp_Close γm h eof $$ []
  · iframe Hinvs Hplan Heof
  (try wp_auto)
  wp_apply wp_Forever as ⟨⟩

theorem wp_Junk
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Forever : wire.Forever.spec (GF := GF) (hG := hG))
    (γm : GName) (h : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ tcpPlan G srvAddr h }}
      (App (Val (@! Junk)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  icases eof_init $$ Hpkg with ⟨%eof, #Heof⟩
  (try wp_auto)
  wp_apply wp_SendJunk wp_Dial wp_ReadFull wp_Write wp_Close γm h eof $$ []
  · iframe Hinvs Hplan Heof
  (try wp_auto)
  wp_apply wp_Forever as ⟨⟩

end proof

end github_com.mit_pdos.etcd_grove.examples.net.echo
end Perennial

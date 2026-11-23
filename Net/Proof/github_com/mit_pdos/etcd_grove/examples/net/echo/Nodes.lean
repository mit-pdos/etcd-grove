/-
The proofs of `examples/net/echo`'s functions, over the specs of `net` and `wire`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `serveConn`: a full read of 5 bytes (`wire.read_acc` on the up-direction: a prefix of the
  dialer's), its echo (a `Write`, Go's loop of steps: the writer predicate `srvP` and the accessor
  `server_write_acc`, over the server's half of the connection's `γ.srv`), and the close
  (`wire.close_drop_au`).
* `Serve`: `Listen`, then the accept loop (`wire.accept_lis_au`: each accepted connection's protocol).
* `Call`: the dial (`echo_dial_au`: `wire.dial_both_au` with the deposits `echo_deposit` and, for an
  abandoned connection, `echo_deposit_ab`), the write of `"hello"` (`wire.writeP`/`wire.write_acc`
  on the up-direction: success means all of it written), the full read of the reply
  (`wire.read_acc` on the down-direction), and the check: the reply is a prefix of `"hello"`
  (`client_check`) of its length, so `"hello"`.
* `SendJunk`: as `Call`, without the check.
* `eof_init`: `io.EOF`'s value, from the package's initialization (the bodies take it, and
  `poll.ErrDeadlineExceeded`'s, `wire.ed_init`). A failure's error, of any kind, is a non-nil
  `*OpError` (`net.resErr_netErr`): every `err != nil` check takes the failure branch.

The commands' `main`s (`cmd/<node>/Main.lean`) call `Serve`, `Call` and `SendJunk`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.Defs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Perennial.Proof.io
public import Net.Proof.net.AtAddr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv sentAll sentLb rcvdAll)

namespace github_com.mit_pdos.etcd_grove.examples.net.echo

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.echo

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
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
    (γm : GName) (c : GoInterface) (cn : Nat) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ net.isConn c cn true srvAddr ∗
        connProto γm cn ∗ globalAddr io.EOF ↦□ eof ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! serveConn)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn echoInvs connProto
  wp_start as ⟨⟨#HaddrInv, #HechoInv⟩, ⟨%t, %la, %ra, %Hct, #Hc⟩,
    ⟨%γ, #Hname, Hend, Htok, Hr, #Hlb0⟩, #Heof, #Hed⟩
  subst Hct
  ihave #HdU := echo_dirInv_up γm cn γ $$ HechoInv Hname
  ihave #HdD := echo_dirInv_down γm cn γ $$ HechoInv Hname
  ihave #Hacc := wire.read_acc echoN cn true γ.up NetEnd.fresh [] $$ [HdU]
  · simp only [Bool.not_true]
    iexact HdU
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 5)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr
      buf _ (wire.readP γ.up cn true NetEnd.fresh []) eof ed $$ [Hbuf Hend Hr]
    as %ok ⟨%got, %bs', HP, Hbuf, %Hres⟩
  · iframe Hbuf Heof Hed Hacc
    isplitr [Hend Hr]
    · unfold net.isConn
      iexists t, la, ra
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
    wp_apply wp_Close t cn true srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
      as %err ⟨%res, -, -⟩
    · iframe Hc
      iapply wire.close_drop_au echoN cn true γ.down _ $$ HdD Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · -- echo the request, then close
    obtain rfl := Hok rfl
    wp_auto
    isimp only [List.nil_append] at Hlb
    wp_apply wp_Write t cn true srvAddr la ra buf got (DFrac.own 1) ed
        (srvP cn γ NetEnd.fresh) $$ [Hbuf Hend Htok]
      as %n %err ⟨%w, %res, HP, Hbuf, -⟩
    · iframe Hc Hbuf Hed
      isplitl [Hend Htok]
      · unfold srvP
        iframe Hend Htok
      iapply server_write_acc γm cn γ NetEnd.fresh got $$ HechoInv Hname Hlb
    unfold srvP
    icases HP with ⟨Hend, -⟩
    (try wp_auto)
    wp_apply wp_Close t cn true srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
      as %err' ⟨%res', -, -⟩
    · iframe Hc
      iapply wire.close_drop_au echoN cn true γ.down _ $$ HdD Hend
    (try wp_auto)
    iapply HΦ
    itrivial


theorem wp_Serve
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗
        ⌜addrOk srvAddr = true⌝ ∗
        globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! Serve)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, %Hpl, #Heof, #Hed⟩
  icases echoInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HechoInv⟩
  (try wp_auto)
  wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp srvAddr $$ []
    as %li %err (⟨%Herr, %l, #Hli, Hlis, #Hla⟩ | ⟨%x, -, #Herr⟩)
  · iframe %Hpl
    iapply wire.listen_au addrN srvAddr _ $$ HaddrInv
  · -- listening: the accept loop
    subst Herr
    unfold net.isListener
    icases Hli with ⟨%t, %x, %Ht, #Hlt⟩
    subst Ht
    wp_auto
    ihave HI : ("Hlis" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) l srvAddr true :
      IProp GF) $$ [Hlis]
    · iexact Hlis
    wp_for HI
    wp_apply (net.Listener.Accept.spec_addrOk wp_Accept) t l x srvAddr
        (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l srvAddr true)
        (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l srvAddr true ∗
          connProto γm cn)) $$ [Hlis]
      as %c %err (⟨%Herr, %cn, #Hc, Hlis, Hproto⟩ | ⟨%k, Hlis, #Herr⟩)
    · iframe Hlt Hla
      iapply wire.accept_lis_au addrN srvAddr (connProto γm) _ l true $$ HaddrInv Hlis
    · -- a connection: serve it
      subst Herr
      wp_auto
      wp_apply wp_serveConn wp_ReadFull wp_Write wp_Close γm c cn eof ed $$ [Hproto]
      · iframe Hinvs Hc Hproto Heof Hed
      wp_for_post
      iframe
    · -- a failure (of any kind): go on
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      wp_auto
      wp_for_post
      iframe
  · -- not listening: return
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    iapply HΦ
    itrivial

/-- The dial's update (`net.Dial`'s, `Qfail := True`): the dialer keeps `dialerOwn` of a new
connection; the deposit of an abandoned one (D16) is `echo_deposit_ab`'s. -/
theorem echo_dial_au (γm : GName) :
    ⊢ inv addrN (addrInv srvAddr (connProto (GF := GF) γm)) -∗ inv echoN (echoState (GF := GF) γm) -∗
      |={⊤,∅}=> ∃ S, netPend G srvAddr S ∗
        ∀ cn, ⌜cn ∉ S⌝ -∗ netPend G srvAddr (S ∪ {[cn]}) -∗ netConnAt G cn srvAddr -∗
          netFresh G cn true -∗
          ((netFresh G cn false ={∅,⊤}=∗ dialerOwn γm cn) ∧
           (netEnd G cn false { NetEnd.fresh with closed := true } -∗
            netDir G cn false ⟨[], .fin⟩ ={∅,⊤}=∗ True)) := by
  iintro #HaddrInv #HechoInv
  iapply wire.dial_both_au addrN srvAddr (connProto γm) (dialerOwn γm) $$ HaddrInv
  · iintro %cn #Hat Hd Ha
    iapply echo_deposit γm cn $$ HechoInv Hat Hd Ha
  · iintro %cn #Hat He Hd Ha
    iapply echo_deposit_ab γm cn $$ HechoInv Hat He Hd Ha

theorem wp_Call
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ ⌜addrOk srvAddr = true⌝ ∗
        globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! Call)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof, #Hed⟩
  icases echoInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HechoInv⟩
  (try wp_auto)
  wp_apply wp_Dial go!"tcp" net.tcpNet_tcp srvAddr iprop(True) (fun cn => dialerOwn γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hown⟩ | ⟨-, %x, -, #Herr⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply echo_dial_au γm $$ HaddrInv HechoInv
  · subst Herr
    unfold dialerOwn
    icases Hown with ⟨%γ, #Hname, Hend, Hw, Hr, #Hlb0⟩
    unfold net.isConn
    icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    ihave #HdU := echo_dirInv_up γm cn γ $$ HechoInv Hname
    ihave #HdD := echo_dirInv_down γm cn γ $$ HechoInv Hname
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Write t cn false srvAddr la ra sl _ (DFrac.own 1) ed
        (wire.writeP γ.up cn false NetEnd.fresh []) $$ [Hsl Hend Hw]
      as %n %err ⟨%w, %res, HP, Hsl, %Hwp, #Herr⟩
    · iframe Hca Hsl Hed
      isplitl [Hend Hw]
      · iapply wire.writeP_init
        iframe Hend Hw
      iapply wire.write_acc echoN cn false γ.up NetEnd.fresh [] _ $$ HdU
    unfold wire.writeP
    icases HP with ⟨Hend, Hw, -⟩
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    by_cases hres : res = none
    case neg =>
      -- the write failed (any kind; a prefix may have been sent): close and return
      obtain ⟨pe, rfl⟩ := Hne.2 hres
      wp_auto
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hca
        iapply wire.close_drop_au echoN cn false γ.up _ $$ HdU Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    subst hres
    obtain rfl := Hne.1 rfl
    obtain ⟨-, -, Hall, -⟩ := Hwp
    obtain rfl := Hall rfl
    wp_auto
    wp_apply (wp_slice_make2 (V := w8) (W64 5)) as %buf ⟨Hbuf, -⟩
    · ipureintro; decide
    (try wp_auto)
    ihave #Hacc := wire.read_acc echoN cn false γ.down NetEnd.fresh [] $$ [HdD]
    · simp only [Bool.not_false]
      iexact HdD
    wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false
        srvAddr buf _ (wire.readP γ.down cn false NetEnd.fresh []) eof ed $$ [Hbuf Hend Hr]
      as %ok ⟨%got, %bs', HP, Hbuf, %Hres⟩
    · iframe Hbuf Heof Hed Hacc
      isplitr [Hend Hr]
      · unfold net.isConn
        iexists t, la, ra
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
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hca
        iapply wire.close_drop_au echoN cn false γ.up _ $$ HdU Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    · -- the reply is a prefix of `"hello"` of its length
      obtain rfl := Hok rfl
      imod client_check' γm cn γ _ ([] ++ got) $$ HechoInv Hname Hw Hlb with ⟨%Hpre, -⟩
      have hs : got = go!"hello" := by
        simp only [List.nil_append] at Hpre
        exact Hpre.eq_of_length (by simpa using Hlen)
      subst hs
      wp_auto
      wp_apply wp_bytes_to_string buf (go!"hello") (DFrac.own 1) $$ Hbuf as Hbuf
      (try wp_auto)
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hca
        iapply wire.close_drop_au echoN cn false γ.up _ $$ HdU Hend
      (try wp_auto)
      iapply HΦ
      itrivial
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    iapply HΦ
    itrivial


theorem wp_SendJunk
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ ⌜addrOk srvAddr = true⌝ ∗
        globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! SendJunk)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof, #Hed⟩
  icases echoInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HechoInv⟩
  (try wp_auto)
  wp_apply wp_Dial go!"tcp" net.tcpNet_tcp srvAddr iprop(True) (fun cn => dialerOwn γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hown⟩ | ⟨-, %x, -, #Herr⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply echo_dial_au γm $$ HaddrInv HechoInv
  · subst Herr
    unfold dialerOwn
    icases Hown with ⟨%γ, #Hname, Hend, Hw, Hr, #Hlb0⟩
    unfold net.isConn
    icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    ihave #HdU := echo_dirInv_up γm cn γ $$ HechoInv Hname
    ihave #HdD := echo_dirInv_down γm cn γ $$ HechoInv Hname
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Write t cn false srvAddr la ra sl _ (DFrac.own 1) ed
        (wire.writeP γ.up cn false NetEnd.fresh []) $$ [Hsl Hend Hw]
      as %n %err ⟨%w, %res, HP, Hsl, -, -⟩
    · iframe Hca Hsl Hed
      isplitl [Hend Hw]
      · iapply wire.writeP_init
        iframe Hend Hw
      iapply wire.write_acc echoN cn false γ.up NetEnd.fresh [] _ $$ HdU
    unfold wire.writeP
    icases HP with ⟨Hend, -, -⟩
    (try wp_auto)
    wp_apply (wp_slice_make2 (V := w8) (W64 3)) as %buf ⟨Hbuf, -⟩
    · ipureintro; decide
    (try wp_auto)
    ihave #Hacc := wire.read_acc echoN cn false γ.down NetEnd.fresh [] $$ [HdD]
    · simp only [Bool.not_false]
      iexact HdD
    wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false
        srvAddr buf _ (wire.readP γ.down cn false NetEnd.fresh []) eof ed $$ [Hbuf Hend Hr]
      as %ok ⟨%got, %bs', HP, Hbuf, -⟩
    · iframe Hbuf Heof Hed Hacc
      isplitr [Hend Hr]
      · unfold net.isConn
        iexists t, la, ra
        iframe Hca
        ipureintro; rfl
      unfold wire.readP
      simp only [List.append_nil]
      iframe Hend Hr Hlb0
    unfold wire.readP
    icases HP with ⟨Hend, -, -⟩
    (try wp_auto)
    wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
      as %err' ⟨%res', -, -⟩
    · iframe Hca
      iapply wire.close_drop_au echoN cn false γ.up _ $$ HdU Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
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

end proof

end github_com.mit_pdos.etcd_grove.examples.net.echo
end Perennial

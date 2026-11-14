/-
The proofs of `examples/net/echo`'s functions, over the specs of `net` and `wire`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `serveConn`: a full read of 5 bytes (a prefix of the dialer's), its echo (`server_write_au`,
  with the connection's token), and the close (`server_close_au`).
* `Serve`: `Listen`, then the accept loop (`wire.accept_au`: each accepted connection's protocol).
* `Call`: the dial (`wire.dial_au`, the deposit `echo_deposit`), the write of `"hello"`, the full
  read of the reply, and the check: the reply is a prefix of `"hello"` (`client_check`) of its
  length, so `"hello"`.
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
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap)

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
theorem client_check' (γm : GName) (cn : Nat) (γ : GName) (out : GoString) (f : Bool)
    (resp : GoString) :
    ⊢ inv echoN (echoState (G (GF := GF)) γm) -∗ echoName G γm cn γ -∗
      tcpOut G cn false out f -∗ tcpOutLb G cn true resp ={⊤}=∗
      ⌜resp <+: out⌝ ∗ tcpOut G cn false out f :=
  client_check γm cn γ out f resp

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
  wp_start as ⟨⟨#HaddrInv, #HechoInv⟩, ⟨%t, %Hct, #Hc⟩, ⟨%γ, Hend, Htok, #Hname⟩, #Heof⟩
  subst Hct
  ihave #Hat := net.connAt_conn t cn true srvAddr $$ Hc
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 5)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  imod tcpOutLb_nil (G (GF := GF)) cn false srvAddr $$ Hat with #Hlb0
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr buf
      _ TcpEnd.fresh 0 [] eof rfl $$ [Hbuf Hend]
    as %ok ⟨%st', %r', %bs', Hend, Hbuf, %Hlen, Hres⟩
  · simp only [Bool.not_true]
    iframe Hbuf Hend Heof Hlb0
    unfold net.isConn
    iexists t
    iframe Hc
    ipureintro; rfl
  cases ok
  · -- the read failed: close
    wp_auto
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
    · iframe Hc
      iapply server_close_au γm cn γ st' r' $$ HechoInv Hname Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · -- echo the request, then close
    simp only [↓reduceIte]
    icases Hres with ⟨%sent, #Hsent, %Hs⟩
    obtain ⟨rfl, rfl, -, hsd⟩ := Hs
    simp only [List.drop_zero] at hsd
    subst hsd
    wp_auto
    wp_apply wp_Write t cn true srvAddr buf sent (DFrac.own 1)
        (fun _ _ => iprop(∃ st'', tcpEnd G cn true st'' (0 + (List.replicate 5 (zero_val w8)).length)))
        $$ [Hbuf Hend Htok]
      as %n %err ⟨%k, %okw, ⟨%st'', Hend⟩, Hbuf, -⟩
    · iframe Hc Hbuf
      iapply server_write_au γm cn γ sent sent TcpEnd.fresh
        (0 + (List.replicate 5 (zero_val w8)).length) (List.prefix_refl _) $$ HechoInv Hname Htok
        Hsent Hend
    (try wp_auto)
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
    · iframe Hc
      iapply server_close_au γm cn γ st'' _ $$ HechoInv Hname Hend
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
  wp_apply wp_Listen srvAddr $$ Hplan as %li %err (⟨%Herr, %l, #Hli, Hlis⟩ | %Herr)
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
    wp_apply wp_Accept t l srvAddr true
        (tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l srvAddr true)
        (fun cn => iprop(tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l srvAddr true ∗
          connProto γm cn)) $$ [Hlis]
      as %c %err (⟨%Herr, %cn, #Hc, Hlis, Hproto⟩ | ⟨%Herr, Hlis⟩)
    · iframe Hlt Hlis
      isplit
      · iintro Hl; iexact Hl
      · imod wire.accept_au addrN srvAddr (connProto γm) $$ HaddrInv with ⟨%S, Hp, Hk⟩
        imodintro
        iexists S
        iframe Hp
        iintro %cn %HcS Hp
        imod Hk $$ %cn %HcS Hp with Hproto
        imodintro
        iintro Hl -
        iframe Hl Hproto
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
  wp_apply wp_Dial srvAddr h iprop(True)
      (fun cn => iprop(tcpFreshEnd G cn false ∗ ∃ γ, echoName G γm cn γ)) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, ⟨Hd, %γ, #Hname⟩⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply wire.dial_au addrN srvAddr (connProto γm) (fun cn => iprop(∃ γ, echoName G γm cn γ))
        $$ HaddrInv
      iintro %cn #Hat Ha
      iapply echo_deposit γm cn $$ HechoInv Hat Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %Hct, #Hca⟩
    subst Hct
    ihave #Hat := net.connAt_conn t cn false srvAddr $$ Hca
    unfold tcpFreshEnd
    icases Hd with ⟨Hend, Hout⟩
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Write t cn false srvAddr sl _ (DFrac.own 1)
        (fun k ok => iprop(∃ st', ⌜WriteRes TcpEnd.fresh (go!"hello") k ok st'⌝ ∗
          tcpEnd G cn false st' 0 ∗ tcpOut G cn false ([] ++ (go!"hello").take k) false))
        $$ [Hsl Hend Hout]
      as %n %err ⟨%k, %okw, ⟨%st', %Hwr, Hend, Hout⟩, Hsl, %Hn⟩
    · iframe Hca Hsl
      iapply wire.owned_write_au cn false _ 0 [] false _ $$ Hend Hout
    obtain ⟨-, Hnil, Herr⟩ := Hn
    cases okw
    · -- the write failed: close and return
      obtain ⟨pe, rfl⟩ := Herr rfl
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend Hout] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply wire.owned_close_drop cn false _ _ _ false $$ Hend Hout
      (try wp_auto)
      iapply HΦ
      itrivial
    rw [Hnil rfl]
    obtain ⟨rfl, rfl⟩ : k = 5 ∧ st' = TcpEnd.fresh := by
      rcases Hwr with ⟨-, -, h, -⟩ | ⟨-, ⟨hk, -, hst⟩ | ⟨-, h, -⟩⟩
      · cases h
      · exact ⟨hk, hst⟩
      · cases h
    wp_auto
    wp_apply (wp_slice_make2 (V := w8) (W64 5)) as %buf ⟨Hbuf, -⟩
    · ipureintro; decide
    (try wp_auto)
    imod tcpOutLb_nil (G (GF := GF)) cn true srvAddr $$ Hat with #Hlb0
    wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false srvAddr
        buf _ TcpEnd.fresh 0 [] eof rfl $$ [Hbuf Hend]
      as %ok ⟨%st'', %r', %bs', Hend, Hbuf, %Hlen, Hres⟩
    · simp only [Bool.not_false]
      iframe Hbuf Hend Heof Hlb0
      unfold net.isConn
      iexists t
      iframe Hca
      ipureintro; rfl
    cases ok
    · -- the read failed: close
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend Hout] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply wire.owned_close_drop cn false _ _ _ false $$ Hend Hout
      (try wp_auto)
      iapply HΦ
      itrivial
    · -- the reply is a prefix of `"hello"` of its length
      simp only [↓reduceIte]
      icases Hres with ⟨%sent, #Hsent, %Hs⟩
      obtain ⟨rfl, rfl, hsl, hsd⟩ := Hs
      simp only [List.drop_zero] at hsd
      subst hsd
      imod client_check' γm cn γ _ false sent $$ HechoInv Hname Hout Hsent with ⟨%Hpre, Hout⟩
      have hs : sent = go!"hello" := by
        simp only [List.nil_append, List.take_of_length_le (by decide : List.length (go!"hello") ≤ 5)] at Hpre
        exact Hpre.eq_of_length (by simpa using hsl)
      subst hs
      wp_auto
      wp_apply wp_bytes_to_string buf (go!"hello") (DFrac.own 1) $$ Hbuf as Hbuf
      (try wp_auto)
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend Hout] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply wire.owned_close_drop cn false _ _ _ false $$ Hend Hout
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
  wp_apply wp_Dial srvAddr h iprop(True)
      (fun cn => iprop(tcpFreshEnd G cn false ∗ ∃ γ, echoName G γm cn γ)) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, ⟨Hd, %γ, #Hname⟩⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply wire.dial_au addrN srvAddr (connProto γm) (fun cn => iprop(∃ γ, echoName G γm cn γ))
        $$ HaddrInv
      iintro %cn #Hat Ha
      iapply echo_deposit γm cn $$ HechoInv Hat Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %Hct, #Hca⟩
    subst Hct
    ihave #Hat := net.connAt_conn t cn false srvAddr $$ Hca
    unfold tcpFreshEnd
    icases Hd with ⟨Hend, Hout⟩
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Write t cn false srvAddr sl _ (DFrac.own 1)
        (fun k ok => iprop(∃ st', tcpEnd G cn false st' 0 ∗
          tcpOut G cn false ([] ++ (go!"xxxxxxxxxx").take k) false))
        $$ [Hsl Hend Hout]
      as %n %err ⟨%k, %okw, ⟨%st', Hend, Hout⟩, Hsl, -⟩
    · iframe Hca Hsl
      imod wire.owned_write_au cn false _ 0 [] false _ $$ Hend Hout
        with ⟨%st0, %r0, %out0, %f0, Hend, Hout, Hk⟩
      imodintro
      iexists st0, r0, out0, f0
      iframe Hend Hout
      iintro %k %ok %st3 %Hwr Hend Hout
      imod Hk $$ %k %ok %st3 %Hwr Hend Hout with ⟨%st4, -, Hend, Hout⟩
      imodintro
      iexists st4
      iframe Hend Hout
    (try wp_auto)
    wp_apply (wp_slice_make2 (V := w8) (W64 3)) as %buf ⟨Hbuf, -⟩
    · ipureintro; decide
    (try wp_auto)
    imod tcpOutLb_nil (G (GF := GF)) cn true srvAddr $$ Hat with #Hlb0
    wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false srvAddr
        buf _ st' 0 [] eof rfl $$ [Hbuf Hend]
      as %ok ⟨%st'', %r', %bs', Hend, Hbuf, -, -⟩
    · simp only [Bool.not_false]
      iframe Hbuf Hend Heof Hlb0
      unfold net.isConn
      iexists t
      iframe Hca
      ipureintro; rfl
    (try wp_auto)
    wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend Hout] as %err' ⟨%ok', -, -⟩
    · iframe Hca
      iapply wire.owned_close_drop cn false _ _ _ false $$ Hend Hout
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

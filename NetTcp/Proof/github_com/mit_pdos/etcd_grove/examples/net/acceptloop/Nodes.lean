/-
The proofs of `examples/net/acceptloop`'s functions, over the specs of `net` and `wire`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `handle`: a full read of 1 byte (a prefix of the dialer's), its echo (`server_write_au`, with
  the connection's token), and the close (`server_close_au`); as echo's `serveConn`.
* `Serve`: `Listen`, then the accept loop (`wire.accept_au`: each accepted connection's
  protocol), which forks a `handle` per connection (`wp_fork`), handing it that connection's
  protocol; the loop keeps only the listener.
* `CallOne id`: the dial (`wire.dial_au`, the deposit `echo_deposit`), the write of `[id]`, the
  full read of the reply, and the check: the reply is a prefix of `[id]` (`client_check`) of
  length 1, so `resp[0] = id`.
* `Call`: two forked `CallOne`s, each with copies of the persistent protocol and plan only (each
  owns the connection it dials, so nothing is shared between them).
* `Server`, `Client`: the bodies, then `wire.Forever`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.Defs
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFullOwned
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
theorem client_check' (γm : GName) (cn : Nat) (γ : GName) (out : GoString) (f : Bool)
    (resp : GoString) :
    ⊢ inv echoN (echoState (G (GF := GF)) γm) -∗ echoName G γm cn γ -∗
      tcpOut G cn false out f -∗ tcpOutLb G cn true resp ={⊤}=∗
      ⌜resp <+: out⌝ ∗ tcpOut G cn false out f :=
  client_check γm cn γ out f resp

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
  wp_start as ⟨⟨#HaddrInv, #HechoInv⟩, ⟨%t, %Hct, #Hc⟩, ⟨%γ, Hend, Htok, #Hname⟩, #Heof⟩
  subst Hct
  ihave #Hat := net.connAt_conn t cn true srvAddr $$ Hc
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  imod tcpOutLb_nil (G (GF := GF)) cn false srvAddr $$ Hat with #Hlb0
  wp_apply wire.ReadFull.owned wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr buf
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
    obtain ⟨rfl, -, hsd⟩ := Hs
    simp only [List.drop_zero] at hsd
    subst hsd
    wp_auto
    wp_apply wp_Write t cn true srvAddr buf sent (DFrac.own 1)
        (fun _ _ => iprop(∃ st'', tcpEnd G cn true st'' (0 + (List.replicate 1 (zero_val w8)).length)))
        $$ [Hbuf Hend Htok]
      as %n %err ⟨%k, %okw, ⟨%st'', Hend⟩, Hbuf, -⟩
    · iframe Hc Hbuf
      iapply server_write_au γm cn γ sent sent _
        (0 + (List.replicate 1 (zero_val w8)).length) (List.prefix_refl _) $$ HechoInv Hname Htok
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
        (fun k ok => iprop(∃ st', ⌜WriteRes TcpEnd.fresh [id] k ok st'⌝ ∗
          tcpEnd G cn false st' 0 ∗ tcpOut G cn false ([] ++ [id].take k) false))
        $$ [Hreq Hend Hout]
      as %n %err ⟨%k, %okw, ⟨%st', %Hwr, Hend, Hout⟩, Hreq, %Hn⟩
    · iframe Hca Hreq
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
    obtain ⟨rfl, rfl⟩ : k = 1 ∧ st' = TcpEnd.fresh := by
      rcases Hwr with ⟨-, -, h, -⟩ | ⟨-, ⟨hk, -, hst⟩ | ⟨-, h, -⟩⟩
      · cases h
      · exact ⟨hk, hst⟩
      · cases h
    wp_auto
    wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
    · ipureintro; decide
    (try wp_auto)
    imod tcpOutLb_nil (G (GF := GF)) cn true srvAddr $$ Hat with #Hlb0
    wp_apply wire.ReadFull.owned wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false srvAddr
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
    · -- the reply is a prefix of `[id]` of its length
      simp only [↓reduceIte]
      icases Hres with ⟨%sent, #Hsent, %Hs⟩
      obtain ⟨rfl, hsl, hsd⟩ := Hs
      simp only [List.drop_zero] at hsd
      subst hsd
      imod client_check' γm cn γ _ false sent $$ HechoInv Hname Hout Hsent with ⟨%Hpre, Hout⟩
      have hs : sent = [id] := by
        simp only [List.nil_append, List.take_of_length_le (by simp : List.length [id] ≤ 1)] at Hpre
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
  (try wp_auto)
  wp_apply wp_fork $$ []
  · wp_apply wp_CallOne wp_Dial wp_ReadFull wp_Write wp_Close γm h eof (W8 1) $$ []
    · iframe Hinvs Hplan Heof
    itrivial
  (try wp_auto)
  wp_apply wp_fork $$ []
  · wp_apply wp_CallOne wp_Dial wp_ReadFull wp_Write wp_Close γm h eof (W8 2) $$ []
    · iframe Hinvs Hplan Heof
    itrivial
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

end proof

end github_com.mit_pdos.etcd_grove.examples.net.acceptloop
end Perennial

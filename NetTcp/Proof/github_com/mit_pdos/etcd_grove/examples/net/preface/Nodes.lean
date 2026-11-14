/-
The proofs of `examples/net/preface`'s functions, over the specs of `net`, `wire` and `time`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `serveConn`: the deadline (`time.Now().Add(time.Second)`, whatever time it is: the model of
  `SetDeadline` does not read it; `owned_setDeadline_au`), a full read of the 4-byte preface, the
  check against `Magic` (both branches: the protocol does not need it), the deadline cleared, a
  full read of the 1-byte request (a prefix of the dialer's bytes past the preface), its echo
  (`server_write_au`, with the connection's token), and the close (`server_close_au`). A failure
  of any operation (a timeout under the deadline among them) needs no reasoning of its own: the
  specs allow every operation to fail.
* `Serve`: `Listen`, then the accept loop (`wire.accept_lis_au`: each accepted connection's protocol).
* `Call`: the dial (`wire.dial_au`, the deposit `pf_deposit`), the writes of `Magic` and of the
  request `[42]`, the full read of the 1-byte reply, and the check: the reply is a prefix of the
  client's bytes past the preface, `[42]` (`client_check`), of its length, so `[42]`.
* `SendJunk`: as `Call`, without the check.
* `Server`, `Client`, `Junk`: the bodies, then `wire.Forever`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.Defs
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFullOwned
public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.Forever
public import NetTcp.Spec.net.Conn__Read
public import NetTcp.Spec.net.Conn__Write
public import NetTcp.Spec.net.Conn__Close
public import NetTcp.Spec.net.Dial
public import NetTcp.Spec.net.Listen
public import NetTcp.Spec.net.Listener__Accept
public import NetTcp.Spec.net.Conn__SetDeadline
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Time__Add
public import Perennial.Proof.io

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap)

namespace github_com.mit_pdos.etcd_grove.examples.net.preface

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.preface

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : preface.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- `client_check`, its update under a node's invariants (`Defs.lean`'s are the global ghost
state's, the same up to unfolding). -/
theorem client_check' (γm : GName) (cn : Nat) (γ : GName) (out : GoString) (f : Bool)
    (resp : GoString) :
    ⊢ inv pfN (pfState (G (GF := GF)) γm) -∗ pfName G γm cn γ -∗
      tcpOut G cn false out f -∗ tcpOutLb G cn true resp ={⊤}=∗
      ⌜resp <+: out.drop preLen⌝ ∗ tcpOut G cn false out f :=
  client_check γm cn γ out f resp

theorem wp_serveConn
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_SetDeadline : net.Conn.SetDeadline.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Add : time.Time.Add.spec (GF := GF) (hG := hG))
    (γm : GName) (c : GoInterface) (cn : Nat) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pfInvs γm ∗ net.isConn c cn true srvAddr ∗
        connProto γm cn ∗ globalAddr io.EOF ↦□ eof }}
      (App (Val (@! serveConn)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn pfInvs connProto
  wp_start as ⟨⟨#HaddrInv, #HpfInv⟩, ⟨%t, %Hct, #Hc⟩, ⟨%γ, Hend, Htok, #Hname⟩, #Heof⟩
  subst Hct
  ihave #Hat := net.connAt_conn t cn true srvAddr $$ Hc
  wp_auto
  wp_apply wp_Now as %tm -
  wp_apply wp_Add as %tm' -
  wp_apply wp_SetDeadline t cn true srvAddr tm' (fun _ => iprop(∃ st', tcpEnd G cn true st' 0))
      $$ [Hend] as %err ⟨%ok, ⟨%st1, Hend⟩, -⟩
  · iframe Hc
    iapply owned_setDeadline_au cn true _ 0 $$ Hend
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w8) (W64 4)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  imod tcpOutLb_nil (G (GF := GF)) cn false srvAddr $$ Hat with #Hlb0
  wp_apply wire.ReadFull.owned wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr buf
      _ st1 0 [] eof rfl $$ [Hbuf Hend]
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
      iapply server_close_au γm cn γ st' r' $$ HpfInv Hname Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · simp only [↓reduceIte]
    icases Hres with ⟨%sent, #Hsent, %Hs⟩
    obtain ⟨rfl, hsl, hsd⟩ := Hs
    simp only [List.drop_zero] at hsd
    subst hsd
    wp_auto
    wp_apply wp_bytes_to_string buf sent (DFrac.own 1) $$ Hbuf as Hbuf
    (try wp_auto)
    by_cases hm : sent = [80#8, 82#8, 73#8, 42#8]
    case neg =>
      -- not the preface: close
      simp only [hm, decide_false, Bool.not_false]
      wp_auto
      wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
      · iframe Hc
        iapply server_close_au γm cn γ _ _ $$ HpfInv Hname Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    simp only [hm, decide_true, Bool.not_true]
    wp_auto
    wp_apply wp_SetDeadline t cn true srvAddr _
        (fun _ => iprop(∃ st', tcpEnd G cn true st' (0 + (List.replicate 4 (zero_val w8)).length)))
        $$ [Hend] as %err ⟨%ok, ⟨%st2, Hend⟩, -⟩
    · iframe Hc
      iapply owned_setDeadline_au cn true _ _ $$ Hend
    (try wp_auto)
    wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %req ⟨Hreq, -⟩
    · ipureintro; decide
    (try wp_auto)
    wp_apply wire.ReadFull.owned wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr
        req _ st2 (0 + (List.replicate 4 (zero_val w8)).length) [80#8, 82#8, 73#8, 42#8] eof
        (by simp) $$ [Hreq Hend]
      as %ok2 ⟨%st3, %r3, %bs3, Hend, Hreq, %Hlen3, Hres2⟩
    · simp only [Bool.not_true]
      iframe Hreq Hend Heof Hsent
      unfold net.isConn
      iexists t
      iframe Hc
      ipureintro; rfl
    cases ok2
    · -- the read failed: close
      wp_auto
      wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hc
        iapply server_close_au γm cn γ _ _ $$ HpfInv Hname Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    · -- reply with the request, then close
      simp only [↓reduceIte]
      icases Hres2 with ⟨%sent2, #Hsent2, %Hs2⟩
      obtain ⟨rfl, -, hsd2⟩ := Hs2
      subst hsd2
      wp_auto
      wp_apply wp_Write t cn true srvAddr req _ (DFrac.own 1)
          (fun _ _ => iprop(∃ st'', tcpEnd G cn true st''
            (0 + (List.replicate 4 (zero_val w8)).length + (List.replicate 1 (zero_val w8)).length)))
          $$ [Hreq Hend Htok]
        as %n %err' ⟨%k, %okw, ⟨%st'', Hend⟩, Hreq, -⟩
      · iframe Hc Hreq
        iapply server_write_au γm cn γ _ sent2 _ _ (by simp [preLen]) $$ HpfInv Hname Htok
          Hsent2 Hend
      (try wp_auto)
      wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err'' ⟨%ok', -, -⟩
      · iframe Hc
        iapply server_close_au γm cn γ st'' _ $$ HpfInv Hname Hend
      (try wp_auto)
      iapply HΦ
      itrivial


theorem wp_Serve
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_SetDeadline : net.Conn.SetDeadline.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Add : time.Time.Add.spec (GF := GF) (hG := hG))
    (γm : GName) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pfInvs γm ∗
        tcpPlan G srvAddr (extLocalGS tcpExt (L := hG.goose_localGS)).host ∗
        globalAddr io.EOF ↦□ eof }}
      (App (Val (@! Serve)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof⟩
  icases pfInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HpfInv⟩
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
      wp_apply wp_serveConn wp_ReadFull wp_Write wp_Close wp_SetDeadline wp_Now wp_Add γm c cn eof $$ [Hproto]
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
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pfInvs γm ∗ tcpPlan G srvAddr h ∗
        globalAddr io.EOF ↦□ eof }}
      (App (Val (@! Call)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof⟩
  icases pfInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HpfInv⟩
  (try wp_auto)
  wp_apply wp_Dial srvAddr h iprop(True)
      (fun cn => iprop(tcpFreshEnd G cn false ∗ ∃ γ, pfName G γm cn γ)) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, ⟨Hd, %γ, #Hname⟩⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply wire.dial_au addrN srvAddr (connProto γm) (fun cn => iprop(∃ γ, pfName G γm cn γ))
        $$ HaddrInv
      iintro %cn #Hat Ha
      iapply pf_deposit γm cn $$ HpfInv Hat Ha
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
        (fun k ok => iprop(∃ st', ⌜WriteRes TcpEnd.fresh (go!"PRI*") k ok st'⌝ ∗
          tcpEnd G cn false st' 0 ∗ tcpOut G cn false ([] ++ (go!"PRI*").take k) false))
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
    obtain ⟨rfl, rfl⟩ : k = 4 ∧ st' = TcpEnd.fresh := by
      rcases Hwr with ⟨-, -, h, -⟩ | ⟨-, ⟨hk, -, hst⟩ | ⟨-, h, -⟩⟩
      · cases h
      · exact ⟨hk, hst⟩
      · cases h
    wp_auto
    wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %req ⟨Hreq, -⟩
    · ipureintro; decide
    (try wp_auto)
    ihave %Hrl := ownSlice_len _ _ _ $$ Hreq
    have Hbl : sint.Z req.len = 1 := by
      obtain ⟨h1, h2⟩ := Hrl; simp only [List.length_replicate] at h1; word
    rw [ite_eq_left (by rw [Hbl]; decide)]
    wp_apply wp_store_slice_index req (sint.Z (W64 0)) _ (W8 42) $$ [$Hreq] as Hreq
    · ipureintro; simp
    rw [show (List.replicate 1 (zero_val w8)).set 0 (W8 42) = [W8 42] from rfl]
    wp_apply wp_Write t cn false srvAddr req _ (DFrac.own 1)
        (fun k ok => iprop(∃ st', ⌜WriteRes TcpEnd.fresh [W8 42] k ok st'⌝ ∗
          tcpEnd G cn false st' 0 ∗
          tcpOut G cn false (([] ++ List.take 4 (go!"PRI*")) ++ [W8 42].take k) false))
        $$ [Hreq Hend Hout]
      as %n2 %err2 ⟨%k2, %okw2, ⟨%st2, %Hwr2, Hend, Hout⟩, Hreq, %Hn2⟩
    · iframe Hca Hreq
      iapply wire.owned_write_au cn false _ 0 _ false _ $$ Hend Hout
    obtain ⟨-, Hnil2, Herr2⟩ := Hn2
    cases okw2
    · -- the write failed: close and return
      obtain ⟨pe, rfl⟩ := Herr2 rfl
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend Hout] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply wire.owned_close_drop cn false _ _ _ false $$ Hend Hout
      (try wp_auto)
      iapply HΦ
      itrivial
    rw [Hnil2 rfl]
    obtain ⟨rfl, rfl⟩ : k2 = 1 ∧ st2 = TcpEnd.fresh := by
      rcases Hwr2 with ⟨-, -, h, -⟩ | ⟨-, ⟨hk, -, hst⟩ | ⟨-, h, -⟩⟩
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
    · -- the reply is a prefix of the request of its length
      simp only [↓reduceIte]
      icases Hres with ⟨%sent, #Hsent, %Hs⟩
      obtain ⟨rfl, hsl, hsd⟩ := Hs
      simp only [List.drop_zero] at hsd
      subst hsd
      imod client_check' γm cn γ _ false sent $$ HpfInv Hname Hout Hsent with ⟨%Hpre, Hout⟩
      have hs : sent = [W8 42] := by
        have hd : (([] ++ List.take 4 (go!"PRI*")) ++ List.take 1 [W8 42]).drop preLen = [W8 42] :=
          rfl
        rw [hd] at Hpre
        exact Hpre.eq_of_length (by simpa using hsl)
      subst hs
      ihave %Hbufl := ownSlice_len _ _ _ $$ Hbuf
      have Hbufz : sint.Z buf.len = 1 := by
        obtain ⟨h1, h2⟩ := Hbufl; simp only [List.length_cons, List.length_nil] at h1; word
      wp_auto
      rw [ite_eq_left (by rw [Hbufz]; decide)]
      wp_apply wp_load_slice_index buf (sint.Z (W64 0)) [W8 42] _ (W8 42) (by decide) $$ [Hbuf]
        as Hbuf
      · iframe Hbuf
        ipureintro; rfl
      (try wp_auto)
      rw [ite_eq_left (by rw [Hbl]; decide)]
      wp_apply wp_load_slice_index req (sint.Z (W64 0)) [W8 42] _ (W8 42) (by decide) $$ [Hreq]
        as Hreq
      · iframe Hreq
        ipureintro; rfl
      wp_auto
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
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pfInvs γm ∗ tcpPlan G srvAddr h ∗
        globalAddr io.EOF ↦□ eof }}
      (App (Val (@! SendJunk)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof⟩
  icases pfInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HpfInv⟩
  (try wp_auto)
  wp_apply wp_Dial srvAddr h iprop(True)
      (fun cn => iprop(tcpFreshEnd G cn false ∗ ∃ γ, pfName G γm cn γ)) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, ⟨Hd, %γ, #Hname⟩⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply wire.dial_au addrN srvAddr (connProto γm) (fun cn => iprop(∃ γ, pfName G γm cn γ))
        $$ HaddrInv
      iintro %cn #Hat Ha
      iapply pf_deposit γm cn $$ HpfInv Hat Ha
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
          tcpOut G cn false ([] ++ (go!"PR").take k) false))
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
    wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
    · ipureintro; decide
    (try wp_auto)
    imod tcpOutLb_nil (G (GF := GF)) cn true srvAddr $$ Hat with #Hlb0
    wp_apply wire.ReadFull.owned wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false srvAddr
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
    (wp_SetDeadline : net.Conn.SetDeadline.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (wp_Add : time.Time.Add.spec (GF := GF) (hG := hG))
    (wp_Forever : wire.Forever.spec (GF := GF) (hG := hG))
    (γm : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pfInvs γm ∗
        tcpPlan G srvAddr (extLocalGS tcpExt (L := hG.goose_localGS)).host }}
      (App (Val (@! Server)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan⟩
  icases eof_init $$ Hpkg with ⟨%eof, #Heof⟩
  (try wp_auto)
  wp_apply wp_Serve wp_Listen wp_Accept wp_ReadFull wp_Write wp_Close wp_SetDeadline wp_Now wp_Add
    γm eof $$ []
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
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pfInvs γm ∗ tcpPlan G srvAddr h }}
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
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pfInvs γm ∗ tcpPlan G srvAddr h }}
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

end github_com.mit_pdos.etcd_grove.examples.net.preface
end Perennial

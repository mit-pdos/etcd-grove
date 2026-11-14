/-
The proofs of `examples/net/preface`'s functions, over the specs of `net`, `wire` and `time`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `serveConn`: the deadline (`time.Now().Add(time.Second)`: whatever it sets or clears, the end's
  state is handed back, `owned_setDeadline_au`; a timeout is just a failed read), a full read of
  the 4-byte preface (`wire.read_acc` on the up direction), the check against `Magic` (both
  branches: the protocol does not need it), the deadline cleared, a full read of the 1-byte
  request (a lower bound of the dialer's bytes past the preface, `sentLb`), its echo
  (`server_write_au`, with the connection's token), and the close (`close_drop_au`). A failure of
  any operation needs no reasoning of its own: the specs allow every operation to fail.
* `Serve`: `Listen`, then the accept loop (`wire.accept_lis_au`: each accepted connection's protocol).
* `Call`: the dial (`pf_dial_au`), the writes of `Magic` and of the request `[42]`
  (`wire.write_au`: the client's written bytes), the full read of the 1-byte reply, and the check:
  the reply is a prefix of the client's bytes past the preface, `[42]` (`client_check`), of its
  length, so `[42]`.
* `SendJunk`: as `Call`, without the check.
* `Server`, `Client`, `Junk`: the bodies, then `wire.Forever`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.Defs
public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
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
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap sentAll sentLb rcvdAll)

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
theorem client_check' (γm : GName) (cn : Nat) (ν : PfNames) (W resp : List w8) :
    ⊢ inv pfN (pfState (Gg := hG.goose_globalGS) γm) -∗ pfName (Gg := hG.goose_globalGS) γm cn ν -∗
      sentAll (Gg := hG.goose_globalGS) ν.up W -∗ sentLb (Gg := hG.goose_globalGS) ν.down resp
      ={⊤}=∗ ⌜resp <+: W.drop preLen⌝ ∗ sentAll (Gg := hG.goose_globalGS) ν.up W :=
  client_check γm cn ν W resp

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
  wp_start as ⟨⟨#HaddrInv, #HpfInv⟩, ⟨%t, %Hct, #Hc⟩, ⟨%ν, Hend, Htok, Hrcv, #Hlb0, #Hname⟩,
    #Heof⟩
  subst Hct
  icases pf_dirInv γm cn ν $$ HpfInv Hname with ⟨#HupInv, #HdownInv⟩
  wp_auto
  wp_apply wp_Now as %tm -
  wp_apply wp_Add as %tm' -
  wp_apply wp_SetDeadline t cn true srvAddr tm' (fun _ => iprop(∃ st', tcpEnd G cn true st'))
      $$ [Hend] as %err ⟨%ok, ⟨%st1, Hend⟩, -⟩
  · iframe Hc
    iapply owned_setDeadline_au cn true _ _ _ $$ Hend
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w8) (W64 4)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr
      buf _ (wire.readP ν.up cn true st1 []) eof $$ [Hbuf Hend Hrcv]
    as %ok ⟨%got, %bs', HP, Hbuf, %Hlen⟩
  · iframe Hbuf Heof
    isplitl []
    · unfold net.isConn
      iexists t
      iframe Hc
      ipureintro; rfl
    isplitl [Hend Hrcv]
    · unfold wire.readP
      simp only [List.append_nil]
      iframe Hend Hrcv Hlb0
    · iapply (wire.read_acc pfN cn true ν.up st1 [])
      simp only [Bool.not_true]
      iexact HupInv
  unfold wire.readP
  icases HP with ⟨Hend, Hrcv, #Hlb⟩
  obtain ⟨-, -, Hgot⟩ := Hlen
  cases ok
  · -- the read failed: close
    wp_auto
    wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
    · iframe Hc
      iapply close_drop_au pfN cn true ν.down st1 $$ HdownInv Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · obtain rfl := Hgot rfl
    wp_auto
    wp_apply wp_bytes_to_string buf got (DFrac.own 1) $$ Hbuf as Hbuf
    (try wp_auto)
    by_cases hm : got = [80#8, 82#8, 73#8, 42#8]
    case neg =>
      -- not the preface: close
      simp only [hm, decide_false, Bool.not_false]
      wp_auto
      wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err ⟨%ok', -, -⟩
      · iframe Hc
        iapply close_drop_au pfN cn true ν.down st1 $$ HdownInv Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    subst hm
    simp only [decide_true, Bool.not_true]
    wp_auto
    wp_apply wp_SetDeadline t cn true srvAddr _ (fun _ => iprop(∃ st', tcpEnd G cn true st'))
        $$ [Hend] as %err ⟨%ok, ⟨%st2, Hend⟩, -⟩
    · iframe Hc
      iapply owned_setDeadline_au cn true _ _ _ $$ Hend
    (try wp_auto)
    wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %req ⟨Hreq, -⟩
    · ipureintro; decide
    (try wp_auto)
    wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true
        srvAddr req _ (wire.readP ν.up cn true st2 ([] ++ [80#8, 82#8, 73#8, 42#8])) eof
        $$ [Hreq Hend Hrcv]
      as %ok2 ⟨%got2, %bs3, HP2, Hreq, %Hlen2⟩
    · iframe Hreq Heof
      isplitl []
      · unfold net.isConn
        iexists t
        iframe Hc
        ipureintro; rfl
      isplitl [Hend Hrcv]
      · unfold wire.readP
        simp only [List.append_nil]
        iframe Hend Hrcv Hlb
      · iapply (wire.read_acc pfN cn true ν.up st2 _)
        simp only [Bool.not_true]
        iexact HupInv
    unfold wire.readP
    icases HP2 with ⟨Hend, -, #Hlb2⟩
    obtain ⟨-, -, Hgot2⟩ := Hlen2
    cases ok2
    · -- the read failed: close
      wp_auto
      wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hc
        iapply close_drop_au pfN cn true ν.down st2 $$ HdownInv Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    · -- reply with the request, then close
      obtain rfl := Hgot2 rfl
      wp_auto
      wp_apply wp_Write t cn true srvAddr req got2 (DFrac.own 1)
          (fun _ _ => iprop(tcpEnd G cn true st2)) $$ [Hreq Hend Htok]
        as %n %err' ⟨%k, %okw, Hend, Hreq, -⟩
      · iframe Hc Hreq
        iapply server_write_au γm cn ν got2 _ st2 (by simp [preLen]) $$ HpfInv Hname Htok
          Hlb2 Hend
      (try wp_auto)
      wp_apply wp_Close t cn true srvAddr (fun _ => iprop(True)) $$ [Hend] as %err'' ⟨%ok', -, -⟩
      · iframe Hc
        iapply close_drop_au pfN cn true ν.down st2 $$ HdownInv Hend
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
      wp_apply wp_serveConn wp_ReadFull wp_Write wp_Close wp_SetDeadline wp_Now wp_Add γm c cn eof
        $$ [Hproto]
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
  wp_apply wp_Dial srvAddr h iprop(True) (fun cn => clientRes γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hcr⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply pf_dial_au γm $$ HaddrInv HpfInv
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %Hct, #Hca⟩
    subst Hct
    unfold clientRes
    icases Hcr with ⟨%ν, Hend, Hsnd, Hrcv, #Hlb0, #Hname⟩
    icases pf_dirInv γm cn ν $$ HpfInv Hname with ⟨#HupInv, #HdownInv⟩
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Write t cn false srvAddr sl _ (DFrac.own 1)
        (fun k ok => iprop(tcpEnd G cn false TcpEnd.fresh ∗
          sentAll ν.up ([] ++ (go!"PRI*").take k) ∗
          ⌜∃ d d', WriteOutcome TcpEnd.fresh d (go!"PRI*") k ok d'⌝))
        $$ [Hsl Hend Hsnd]
      as %n %err ⟨%k, %okw, ⟨Hend, Hsnd, %Hwr⟩, Hsl, %Hn⟩
    · iframe Hca Hsl
      iapply wire.write_au pfN cn false ν.up TcpEnd.fresh [] _ $$ HupInv Hend Hsnd
    obtain ⟨-, Hnil, Herr⟩ := Hn
    cases okw
    · -- the write failed: close and return
      obtain ⟨pe, rfl⟩ := Herr rfl
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply close_drop_au pfN cn false ν.up _ $$ HupInv Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    rw [Hnil rfl]
    obtain rfl : k = 4 := by
      obtain ⟨d, d', Hw⟩ := Hwr
      exact wire.writeOutcome_ok Hw
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
        (fun k ok => iprop(tcpEnd G cn false TcpEnd.fresh ∗
          sentAll ν.up (([] ++ (go!"PRI*").take 4) ++ [W8 42].take k) ∗
          ⌜∃ d d', WriteOutcome TcpEnd.fresh d [W8 42] k ok d'⌝))
        $$ [Hreq Hend Hsnd]
      as %n2 %err2 ⟨%k2, %okw2, ⟨Hend, Hsnd, %Hwr2⟩, Hreq, %Hn2⟩
    · iframe Hca Hreq
      iapply wire.write_au pfN cn false ν.up TcpEnd.fresh _ _ $$ HupInv Hend Hsnd
    obtain ⟨-, Hnil2, Herr2⟩ := Hn2
    cases okw2
    · -- the write failed: close and return
      obtain ⟨pe, rfl⟩ := Herr2 rfl
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply close_drop_au pfN cn false ν.up _ $$ HupInv Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    rw [Hnil2 rfl]
    obtain rfl : k2 = 1 := by
      obtain ⟨d, d', Hw⟩ := Hwr2
      exact wire.writeOutcome_ok Hw
    wp_auto
    wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
    · ipureintro; decide
    (try wp_auto)
    wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false
        srvAddr buf _ (wire.readP ν.down cn false TcpEnd.fresh []) eof $$ [Hbuf Hend Hrcv]
      as %ok ⟨%got, %bs', HP, Hbuf, %Hlen⟩
    · iframe Hbuf Heof
      isplitl []
      · unfold net.isConn
        iexists t
        iframe Hca
        ipureintro; rfl
      isplitl [Hend Hrcv]
      · unfold wire.readP
        simp only [List.append_nil]
        iframe Hend Hrcv Hlb0
      · iapply (wire.read_acc pfN cn false ν.down TcpEnd.fresh [])
        simp only [Bool.not_false]
        iexact HdownInv
    unfold wire.readP
    icases HP with ⟨Hend, -, #Hlb⟩
    obtain ⟨Hbl', -, Hgot⟩ := Hlen
    cases ok
    · -- the read failed: close
      wp_auto
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply close_drop_au pfN cn false ν.up _ $$ HupInv Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    · -- the reply is a prefix of the request of its length
      obtain rfl := Hgot rfl
      imod client_check' γm cn ν _ _ $$ HpfInv Hname Hsnd Hlb with ⟨%Hpre, Hsnd⟩
      have hs : got = [W8 42] := by
        have hd : (([] ++ List.take 4 (go!"PRI*")) ++ List.take 1 [W8 42]).drop preLen = [W8 42] :=
          rfl
        rw [hd, List.nil_append] at Hpre
        exact Hpre.eq_of_length (by simpa using Hbl')
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
      wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
      · iframe Hca
        iapply close_drop_au pfN cn false ν.up _ $$ HupInv Hend
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
  wp_apply wp_Dial srvAddr h iprop(True) (fun cn => clientRes γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hcr⟩ | ⟨%Herr, -⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply pf_dial_au γm $$ HaddrInv HpfInv
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %Hct, #Hca⟩
    subst Hct
    unfold clientRes
    icases Hcr with ⟨%ν, Hend, Hsnd, Hrcv, #Hlb0, #Hname⟩
    icases pf_dirInv γm cn ν $$ HpfInv Hname with ⟨#HupInv, #HdownInv⟩
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Write t cn false srvAddr sl _ (DFrac.own 1)
        (fun k ok => iprop(tcpEnd G cn false TcpEnd.fresh ∗
          sentAll ν.up ([] ++ (go!"PR").take k) ∗
          ⌜∃ d d', WriteOutcome TcpEnd.fresh d (go!"PR") k ok d'⌝))
        $$ [Hsl Hend Hsnd]
      as %n %err ⟨%k, %okw, ⟨Hend, -, -⟩, Hsl, -⟩
    · iframe Hca Hsl
      iapply wire.write_au pfN cn false ν.up TcpEnd.fresh [] _ $$ HupInv Hend Hsnd
    (try wp_auto)
    wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
    · ipureintro; decide
    (try wp_auto)
    wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false
        srvAddr buf _ (wire.readP ν.down cn false TcpEnd.fresh []) eof $$ [Hbuf Hend Hrcv]
      as %ok ⟨%got, %bs', HP, Hbuf, -⟩
    · iframe Hbuf Heof
      isplitl []
      · unfold net.isConn
        iexists t
        iframe Hca
        ipureintro; rfl
      isplitl [Hend Hrcv]
      · unfold wire.readP
        simp only [List.append_nil]
        iframe Hend Hrcv Hlb0
      · iapply (wire.read_acc pfN cn false ν.down TcpEnd.fresh [])
        simp only [Bool.not_false]
        iexact HdownInv
    unfold wire.readP
    icases HP with ⟨Hend, -, -⟩
    (try wp_auto)
    wp_apply wp_Close t cn false srvAddr (fun _ => iprop(True)) $$ [Hend] as %err' ⟨%ok', -, -⟩
    · iframe Hca
      iapply close_drop_au pfN cn false ν.up _ $$ HupInv Hend
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

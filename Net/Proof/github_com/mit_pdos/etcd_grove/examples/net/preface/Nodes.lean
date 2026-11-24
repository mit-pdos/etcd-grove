/-
The proofs of `examples/net/preface`'s functions, over the specs of `net`, `wire` and `time`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `serveConn`: the deadline (`time.Now().Add(time.Second)`: whatever it sets or clears, the end's
  state is handed back, `owned_setDeadline_au`; a timeout is just a failed read, of kind `timeout`),
  a full read of the 4-byte preface (`wire.read_acc` on the up direction), the check against
  `Magic` (both branches: the protocol does not need it), the deadline cleared, a full read of the
  1-byte request (a lower bound of the dialer's bytes past the preface, `sentLb`), its echo
  (a `Write`, Go's loop of steps: its writer predicate `srvP`, the server's progress on the reply,
  and its accessor `server_write_acc`), and the close (`wire.close_drop_au`). A failure
  of any operation, of any kind, needs no reasoning of its own: the specs allow every operation to
  fail, and the server checks only `ReadFull`'s result.
* `Serve`: `Listen` (of the plan address itself, `listenAt_self`), then the accept loop
  (`wire.accept_lis_au`: each accepted connection's protocol, also an abandoned dial's).
* `Call`: the dial (`pf_dial_au`; a failed dial, abandoned or not, returns a non-nil error, so the
  client returns), the writes of `Magic` and of the request `[42]` (each a loop of steps, through
  `wire.writeP`/`wire.write_acc`: the client's written bytes; an error, of whatever kind, a non-nil
  `*OpError`, `net.resErr_netErr`, makes it close and return; no error means all written, the
  spec's post), the full read of the 1-byte
  reply, and the check: the reply is a prefix of the client's bytes past the preface, `[42]`
  (`client_check`), of its length, so `[42]`.
* `SendJunk`: as `Call`, without the check.

Each is the body of one of the example's commands (`cmd/*/Main.lean`), which gets `io.EOF`'s value
(`eof_init`) from the package's initialization and `poll.ErrDeadlineExceeded`'s from `wire`'s
(`wire.ed_init`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.Defs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Net.Spec.net.Conn__SetDeadline
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Time__Add
public import Perennial.Proof.io
public import Net.Proof.net.AtAddr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv sentAll sentLb rcvdAll)

namespace github_com.mit_pdos.etcd_grove.examples.net.preface

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.preface

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : preface.Assumptions]
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
    (γm : GName) (c : GoInterface) (cn : Nat) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pfInvs γm ∗ net.isConn c cn true srvAddr ∗
        connProto γm cn ∗ globalAddr io.EOF ↦□ eof ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! serveConn)) (Val #c))
    {{ RET #(); True }} := by
  unfold pfInvs connProto
  wp_start as ⟨⟨#HaddrInv, #HpfInv⟩, #HisConn, ⟨%ν, Hend, Hsrv, Hrcv, #Hlb0, #Hname⟩,
    #Heof, #Hed⟩
  iunfold net.isConn at HisConn
  icases HisConn with ⟨%t, %la, %ra, %Hct, #Hc⟩
  subst Hct
  icases pf_dirInv γm cn ν $$ HpfInv Hname with ⟨#HupInv, #HdownInv⟩
  wp_auto
  wp_apply wp_Now as %tm -
  wp_apply wp_Add as %tm' -
  wp_apply wp_SetDeadline t cn true srvAddr la ra tm' (fun _ => iprop(∃ st', netEnd G cn true st'))
      $$ [Hend] as %err ⟨%res, ⟨%st1, Hend⟩, -⟩
  · iframe Hc
    iapply owned_setDeadline_au cn true _ _ _ $$ Hend
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w8) (W64 4)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr
      buf _ (wire.readP ν.up cn true st1 []) eof ed $$ [Hbuf Hend Hrcv]
    as %ok ⟨%got, %bs', HP, Hbuf, %Hlen⟩
  · iframe Hbuf Heof Hed
    isplitl []
    · unfold net.isConn
      iexists t, la, ra
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
    wp_apply wp_Close t cn true srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
      as %err ⟨%res', -, -⟩
    · iframe Hc
      iapply wire.close_drop_au pfN cn true ν.down st1 $$ HdownInv Hend
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
      wp_apply wp_Close t cn true srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err ⟨%res', -, -⟩
      · iframe Hc
        iapply wire.close_drop_au pfN cn true ν.down st1 $$ HdownInv Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    subst hm
    simp only [decide_true, Bool.not_true]
    wp_auto
    wp_apply wp_SetDeadline t cn true srvAddr la ra _
        (fun _ => iprop(∃ st', netEnd G cn true st')) $$ [Hend] as %err ⟨%res, ⟨%st2, Hend⟩, -⟩
    · iframe Hc
      iapply owned_setDeadline_au cn true _ _ _ $$ Hend
    (try wp_auto)
    wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %req ⟨Hreq, -⟩
    · ipureintro; decide
    (try wp_auto)
    wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true
        srvAddr req _ (wire.readP ν.up cn true st2 ([] ++ [80#8, 82#8, 73#8, 42#8])) eof ed
        $$ [Hreq Hend Hrcv]
      as %ok2 ⟨%got2, %bs3, HP2, Hreq, %Hlen2⟩
    · iframe Hreq Heof Hed
      isplitl []
      · unfold net.isConn
        iexists t, la, ra
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
      wp_apply wp_Close t cn true srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hc
        iapply wire.close_drop_au pfN cn true ν.down st2 $$ HdownInv Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    · -- reply with the request, then close
      obtain rfl := Hgot2 rfl
      wp_auto
      wp_apply wp_Write t cn true srvAddr la ra req got2 (DFrac.own 1) ed
          (srvP cn ν st2) $$ [Hreq Hend Hsrv]
        as %n %err' ⟨%w, %resw, HP, Hreq, -, -⟩
      · iframe Hc Hreq Hed
        isplitl [Hend Hsrv]
        · unfold srvP
          iframe Hend Hsrv
        iapply server_write_acc γm cn ν got2 _ st2 (by simp [preLen]) $$ HpfInv Hname Hlb2
      unfold srvP
      icases HP with ⟨Hend, -⟩
      (try wp_auto)
      wp_apply wp_Close t cn true srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err'' ⟨%res', -, -⟩
      · iframe Hc
        iapply wire.close_drop_au pfN cn true ν.down st2 $$ HdownInv Hend
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
    (γm : GName) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pfInvs γm ∗
        ⌜addrOk srvAddr = true⌝ ∗
        globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! Serve)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, %Hplan, #Heof, #Hed⟩
  icases pfInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HpfInv⟩
  (try wp_auto)
  wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp srvAddr $$ [] as %li %err
    (⟨%Herr, %l, #Hli, Hlis, #Hla⟩ | ⟨%x, -, #Herr⟩)
  · iframe %Hplan
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
      wp_apply wp_serveConn wp_ReadFull wp_Write wp_Close wp_SetDeadline wp_Now wp_Add γm c cn eof
        ed $$ [Hproto]
      · iframe Hinvs Hc Hproto Heof Hed
      wp_for_post
      iframe
    · -- a failure, of either kind: go on
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Herr'
      obtain ⟨pe, rfl⟩ := Herr'.2 (by simp)
      wp_auto
      wp_for_post
      iframe
  · -- not listening: return
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Herr'
    obtain ⟨pe, rfl⟩ := Herr'.2 (by simp)
    wp_auto
    iapply HΦ
    itrivial


theorem wp_Call
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pfInvs γm ∗ ⌜addrOk srvAddr = true⌝ ∗
        globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! Call)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof, #Hed⟩
  icases pfInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HpfInv⟩
  (try wp_auto)
  wp_apply wp_Dial go!"tcp" net.tcpNet_tcp srvAddr iprop(True) (fun cn => clientRes γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hcr⟩ | ⟨-, %x, -, #Herr⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply pf_dial_au γm $$ HaddrInv HpfInv
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    unfold clientRes
    icases Hcr with ⟨%ν, Hend, Hsnd, Hrcv, #Hlb0, #Hname⟩
    icases pf_dirInv γm cn ν $$ HpfInv Hname with ⟨#HupInv, #HdownInv⟩
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Write t cn false srvAddr la ra sl _ (DFrac.own 1) ed
        (wire.writeP ν.up cn false NetEnd.fresh []) $$ [Hsl Hend Hsnd]
      as %n %err ⟨%w, %resw, HP, Hsl, %Hw, #Herr⟩
    · iframe Hca Hsl Hed
      isplitl [Hend Hsnd]
      · iapply wire.writeP_init
        iframe Hend Hsnd
      iapply wire.write_acc pfN cn false ν.up NetEnd.fresh [] _ $$ HupInv
    unfold wire.writeP
    icases HP with ⟨Hend, Hsnd, -⟩
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Herr'
    cases resw
    case some ek =>
      -- the write failed: close and return
      obtain ⟨pe, rfl⟩ := Herr'.2 (by simp)
      wp_auto
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hca
        iapply wire.close_drop_au pfN cn false ν.up _ $$ HupInv Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    rw [Herr'.1 rfl]
    obtain rfl : w = go!"PRI*" := Hw.2.2.1 rfl
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
    wp_apply wp_Write t cn false srvAddr la ra req _ (DFrac.own 1) ed
        (wire.writeP ν.up cn false NetEnd.fresh ([] ++ go!"PRI*")) $$ [Hreq Hend Hsnd]
      as %n2 %err2 ⟨%w2, %resw2, HP, Hreq, %Hw2, #Herr2⟩
    · iframe Hca Hreq Hed
      isplitl [Hend Hsnd]
      · iapply wire.writeP_init
        iframe Hend Hsnd
      iapply wire.write_acc pfN cn false ν.up NetEnd.fresh _ _ $$ HupInv
    unfold wire.writeP
    icases HP with ⟨Hend, Hsnd, -⟩
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr2 with %Herr2'
    cases resw2
    case some ek =>
      -- the write failed: close and return
      obtain ⟨pe, rfl⟩ := Herr2'.2 (by simp)
      wp_auto
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hca
        iapply wire.close_drop_au pfN cn false ν.up _ $$ HupInv Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    rw [Herr2'.1 rfl]
    obtain rfl : w2 = [W8 42] := Hw2.2.2.1 rfl
    wp_auto
    wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
    · ipureintro; decide
    (try wp_auto)
    wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false
        srvAddr buf _ (wire.readP ν.down cn false NetEnd.fresh []) eof ed $$ [Hbuf Hend Hrcv]
      as %ok ⟨%got, %bs', HP, Hbuf, %Hlen⟩
    · iframe Hbuf Heof Hed
      isplitl []
      · unfold net.isConn
        iexists t, la, ra
        iframe Hca
        ipureintro; rfl
      isplitl [Hend Hrcv]
      · unfold wire.readP
        simp only [List.append_nil]
        iframe Hend Hrcv Hlb0
      · iapply (wire.read_acc pfN cn false ν.down NetEnd.fresh [])
        simp only [Bool.not_false]
        iexact HdownInv
    unfold wire.readP
    icases HP with ⟨Hend, -, #Hlb⟩
    obtain ⟨Hbl', -, Hgot⟩ := Hlen
    cases ok
    · -- the read failed: close
      wp_auto
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hca
        iapply wire.close_drop_au pfN cn false ν.up _ $$ HupInv Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    · -- the reply is a prefix of the request of its length
      obtain rfl := Hgot rfl
      imod client_check' γm cn ν _ _ $$ HpfInv Hname Hsnd Hlb with ⟨%Hpre, Hsnd⟩
      have hs : got = [W8 42] := by
        have hd : (([] ++ go!"PRI*") ++ [W8 42]).drop preLen = [W8 42] := rfl
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
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hca
        iapply wire.close_drop_au pfN cn false ν.up _ $$ HupInv Hend
      (try wp_auto)
      iapply HΦ
      itrivial
  · -- the dial failed (abandoned or not): return
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Herr'
    obtain ⟨pe, rfl⟩ := Herr'.2 (by simp)
    wp_auto
    iapply HΦ
    itrivial


theorem wp_SendJunk
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pfInvs γm ∗ ⌜addrOk srvAddr = true⌝ ∗
        globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! SendJunk)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof, #Hed⟩
  icases pfInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HpfInv⟩
  (try wp_auto)
  wp_apply wp_Dial go!"tcp" net.tcpNet_tcp srvAddr iprop(True) (fun cn => clientRes γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hcr⟩ | ⟨-, %x, -, #Herr⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply pf_dial_au γm $$ HaddrInv HpfInv
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    unfold clientRes
    icases Hcr with ⟨%ν, Hend, Hsnd, Hrcv, #Hlb0, #Hname⟩
    icases pf_dirInv γm cn ν $$ HpfInv Hname with ⟨#HupInv, #HdownInv⟩
    wp_auto
    wp_apply wp_string_to_bytes with %sl ⟨Hsl, -⟩
    (try wp_auto)
    wp_apply wp_Write t cn false srvAddr la ra sl _ (DFrac.own 1) ed
        (wire.writeP ν.up cn false NetEnd.fresh []) $$ [Hsl Hend Hsnd]
      as %n %err ⟨%w, %resw, HP, Hsl, -, -⟩
    · iframe Hca Hsl Hed
      isplitl [Hend Hsnd]
      · iapply wire.writeP_init
        iframe Hend Hsnd
      iapply wire.write_acc pfN cn false ν.up NetEnd.fresh [] _ $$ HupInv
    unfold wire.writeP
    icases HP with ⟨Hend, -, -⟩
    (try wp_auto)
    wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
    · ipureintro; decide
    (try wp_auto)
    wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false
        srvAddr buf _ (wire.readP ν.down cn false NetEnd.fresh []) eof ed $$ [Hbuf Hend Hrcv]
      as %ok ⟨%got, %bs', HP, Hbuf, -⟩
    · iframe Hbuf Heof Hed
      isplitl []
      · unfold net.isConn
        iexists t, la, ra
        iframe Hca
        ipureintro; rfl
      isplitl [Hend Hrcv]
      · unfold wire.readP
        simp only [List.append_nil]
        iframe Hend Hrcv Hlb0
      · iapply (wire.read_acc pfN cn false ν.down NetEnd.fresh [])
        simp only [Bool.not_false]
        iexact HdownInv
    unfold wire.readP
    icases HP with ⟨Hend, -, -⟩
    (try wp_auto)
    wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
      as %err' ⟨%res', -, -⟩
    · iframe Hca
      iapply wire.close_drop_au pfN cn false ν.up _ $$ HupInv Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · -- the dial failed (abandoned or not): return
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Herr'
    obtain ⟨pe, rfl⟩ := Herr'.2 (by simp)
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

end github_com.mit_pdos.etcd_grove.examples.net.preface
end Perennial

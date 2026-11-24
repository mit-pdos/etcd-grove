/-
The proofs of `examples/net/acceptloop`'s functions, over the specs of `net` and `wire`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `handle`: a full read of 1 byte (`wire.read_acc` on the up direction: what it read, the dialer
  wrote), its echo (a `Write`, Go's loop of steps: `server_write_acc`, each step extending the
  server's written bytes, still a prefix of the request), and the close
  (`wire.close_drop_au`); as echo's `serveConn`.
* `Serve`: `Listen`, then the accept loop (`wire.accept_lis_au`: each accepted connection's
  protocol), which forks a `handle` per connection (`wp_fork`), handing it that connection's
  protocol; the loop keeps only the listener.
* `CallOne id`: the dial (`wire.dial_both_au`, the registration `echo_register`), the write of
  `[id]` (`wire.writeP`/`wire.write_acc` on the up direction: on success all of it written), the
  full read of the reply (`wire.read_acc` on the down direction), and the check: the reply is a
  prefix of `[id]` (`client_check`) of length 1, so `resp[0] = id`.
* `Call`: two forked `CallOne`s, each with copies of the persistent protocol and plan only (each
  owns the connection it dials, so nothing is shared between them), joined by a wait group:
  Perennial's join idiom (`sync.join`), its `Add(2)` by `wp_Add_many` (`Join.lean`), each
  goroutine's `Done` with `True`, the `Wait` with nothing to collect. The `sync` specs are
  hypotheses, as `net`'s.
* `eof_init`: `io.EOF`'s value, from the package's initialization (the commands' `main`s,
  `cmd/*/Main.lean`, call the bodies with it and with `poll.ErrDeadlineExceeded`'s, `wire.ed_init`,
  which `ReadFull` and `Write` take, the `Err` of a timeout).

Every failure is an `*OpError` (`net.resErr` of its kind, D14), so non-nil (`net.resErr_netErr`):
each `err != nil` check sees it, whatever the kind; no proof distinguishes the kinds. The dial's
update has a second branch, the abandoned connection's (D16, `echo_register_ab`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.Defs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.Join
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Done
public import Perennial.Spec.sync.WaitGroup__Wait
public import Perennial.Proof.io
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Net.Proof.net.AtAddr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv sentAll sentLb rcvdAll)

namespace github_com.mit_pdos.etcd_grove.examples.net.acceptloop

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.acceptloop

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
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
    (γm : GName) (c : GoInterface) (cn : Nat) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ net.isConn c cn true srvAddr ∗
        connProto γm cn ∗ globalAddr io.EOF ↦□ eof ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! handle)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn echoInvs connProto
  wp_start as ⟨⟨#HaddrInv, #HechoInv⟩, ⟨%t, %la, %ra, %Hct, #Hc⟩,
    ⟨%γ, Hend, Hsv, Hru, #Hlbu, #Hname⟩, #Heof, #Hed⟩
  subst Hct
  ihave #Hup := dir_inv γm cn γ false $$ HechoInv Hname
  ihave #Hdown := dir_inv γm cn γ true $$ HechoInv Hname
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn true srvAddr
      buf _ (wire.readP (γ.dir false) cn true NetEnd.fresh []) eof ed $$ [Hbuf Hend Hru]
    as %ok ⟨%got, %bs', HP, Hbuf, %Hlen⟩
  · iframe Hbuf Heof Hed
    isplitr [Hend Hru]
    · unfold net.isConn
      iexists t, la, ra
      iframe Hc
      ipureintro; rfl
    isplitl [Hend Hru]
    · unfold wire.readP; rw [List.append_nil]
      iframe Hend Hru Hlbu
    iapply wire.read_acc echoN cn true (γ.dir false) NetEnd.fresh []
    simp only [Bool.not_true]
    iexact Hup
  iunfold wire.readP at HP
  icases HP with ⟨Hend, Hru, #Hlb⟩
  rw [List.nil_append]
  cases ok
  · -- the read failed: close
    wp_auto
    wp_apply wp_Close t cn true srvAddr la ra (fun _ => iprop(True)) $$ [Hend] as %err ⟨%res, -, -⟩
    · iframe Hc
      iapply wire.close_drop_au echoN cn true (γ.dir true) NetEnd.fresh $$ Hdown Hend
    (try wp_auto)
    iapply HΦ
    itrivial
  · -- echo the request, then close
    (try simp only [↓reduceIte])
    obtain ⟨-, -, Hgot⟩ := Hlen
    have Hgot := Hgot rfl
    subst Hgot
    wp_auto
    wp_apply wp_Write t cn true srvAddr la ra buf got (DFrac.own 1) ed
        (srvP γ cn NetEnd.fresh) $$ [Hbuf Hend Hsv]
      as %n %err ⟨%w, %resw, HP, Hbuf, -, -⟩
    · iframe Hc Hbuf Hed
      isplitl [Hend Hsv]
      · unfold srvP
        iframe Hend Hsv
      iapply server_write_acc γm cn γ got got NetEnd.fresh (List.prefix_refl _) $$ HechoInv Hname
        Hlb
    iunfold srvP at HP
    icases HP with ⟨Hend, -⟩
    (try wp_auto)
    wp_apply wp_Close t cn true srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
      as %err' ⟨%res, -, -⟩
    · iframe Hc
      iapply wire.close_drop_au echoN cn true (γ.dir true) NetEnd.fresh $$ Hdown Hend
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
  wp_start as ⟨#Hinvs, %Hla0, #Heof, #Hed⟩
  icases echoInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HechoInv⟩
  (try wp_auto)
  wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp srvAddr as %li %err (⟨%Herr, %l, #Hli, Hlis, #Hla⟩ | ⟨%x, %ex, -, #HE, -⟩)
  · iframe %Hla0
    iapply wire.listen_au addrN srvAddr _ $$ HaddrInv
  · -- listening: the accept loop
    subst Herr
    unfold net.isListener
    icases Hli with ⟨%t, %xl, %Ht, #Hlt⟩
    subst Ht
    wp_auto
    ihave HI : ("Hlis" ∷ netLis (extLocalGS netExt (L := hG.goose_localGS)) l srvAddr true :
      IProp GF) $$ [Hlis]
    · iexact Hlis
    wp_for HI
    wp_apply (net.Listener.Accept.spec_addrOk wp_Accept) t l xl srvAddr
        (fun _ => netLis (extLocalGS netExt (L := hG.goose_localGS)) l srvAddr true)
        (fun cn => iprop(netLis (extLocalGS netExt (L := hG.goose_localGS)) l srvAddr true ∗
          connProto γm cn)) $$ [Hlis]
      as %c %err (⟨%Herr, %cn, #Hc, Hlis, Hproto⟩ | ⟨%k, Hlis, #HE⟩)
    · iframe Hlt Hla
      iapply wire.accept_lis_au addrN srvAddr (connProto γm) _ l true $$ HaddrInv Hlis
    · -- a connection: its handler, in a goroutine of its own
      subst Herr
      wp_auto
      wp_apply wp_fork $$ [Hproto]
      · wp_apply wp_handle wp_ReadFull wp_Write wp_Close γm c cn eof ed $$ [Hproto]
        · iframe Hinvs Hc Hproto Heof Hed
        itrivial
      (try wp_auto)
      wp_for_post
      iframe
    · -- a failure: go on
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      wp_auto
      wp_for_post
      iframe
  · -- not listening: return
    icases net.opErr_netErr _ _ _ _ _ $$ HE with %Hne
    obtain ⟨pe, rfl⟩ := Hne
    wp_auto
    iapply HΦ
    itrivial


theorem wp_CallOne
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_ReadFull : wire.ReadFull.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (eof ed : GoInterface) (id : w8) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ ⌜addrOk srvAddr = true⌝ ∗
        globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! CallOne)) (Val #id))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof, #Hed⟩
  icases echoInvs_elim γm $$ Hinvs with ⟨#HaddrInv, #HechoInv⟩
  (try wp_auto)
  wp_apply wp_Dial go!"tcp" net.tcpNet_tcp srvAddr iprop(True) (fun cn => dialerOwn γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hown⟩ | ⟨-, %x, -, #HE⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply wire.dial_both_au addrN srvAddr (connProto γm) (dialerOwn γm) $$ HaddrInv
      · iintro %cn #Hat Hd Ha
        iapply echo_register γm cn $$ HechoInv Hd Ha
      · iintro %cn #Hat He Hd Ha
        iapply echo_register_ab γm cn $$ HechoInv He Hd Ha
  · subst Herr
    unfold net.isConn
    icases Hc with ⟨%t, %la, %ra, %Hct, #Hca⟩
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
    wp_apply wp_Write t cn false srvAddr la ra req [id] (DFrac.own 1) ed
        (wire.writeP (γ.dir false) cn false NetEnd.fresh []) $$ [Hreq Hend Hsu]
      as %n %err ⟨%w, %resw, HP, Hreq, %Hw, #HE⟩
    · iframe Hca Hreq Hed
      isplitl [Hend Hsu]
      · iapply wire.writeP_init
        iframe Hend Hsu
      iapply wire.write_acc echoN cn false (γ.dir false) NetEnd.fresh [] [id] $$ Hup
    iunfold wire.writeP at HP
    icases HP with ⟨Hend, Hsu, -⟩
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
    cases resw with
    | some e =>
      -- the write failed: close and return
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      wp_auto
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hca
        iapply wire.close_drop_au echoN cn false (γ.dir false) NetEnd.fresh $$ Hup Hend
      (try wp_auto)
      iapply HΦ
      itrivial
    | none =>
    rw [Hne.1 rfl]
    have hw : w = [id] := Hw.2.2.1 rfl
    subst hw
    wp_auto
    wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
    · ipureintro; decide
    (try wp_auto)
    wp_apply wp_ReadFull (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t) cn false
        srvAddr buf _ (wire.readP (γ.dir true) cn false NetEnd.fresh []) eof ed
        $$ [Hbuf Hend Hrd]
      as %ok ⟨%got, %bs', HP, Hbuf, %Hlen⟩
    · iframe Hbuf Heof Hed
      isplitr [Hend Hrd]
      · unfold net.isConn
        iexists t, la, ra
        iframe Hca
        ipureintro; rfl
      isplitl [Hend Hrd]
      · unfold wire.readP; rw [List.append_nil]
        iframe Hend Hrd Hlbd
      iapply wire.read_acc echoN cn false (γ.dir true) NetEnd.fresh []
      simp only [Bool.not_false]
      iexact Hdown
    iunfold wire.readP at HP
    icases HP with ⟨Hend, Hrd, #Hlb⟩
    simp only [List.nil_append]
    cases ok
    · -- the read failed: close
      wp_auto
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hca
        iapply wire.close_drop_au echoN cn false (γ.dir false) NetEnd.fresh $$ Hup Hend
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
      wp_apply wp_Close t cn false srvAddr la ra (fun _ => iprop(True)) $$ [Hend]
        as %err' ⟨%res', -, -⟩
      · iframe Hca
        iapply wire.close_drop_au echoN cn false (γ.dir false) NetEnd.fresh $$ Hup Hend
      (try wp_auto)
      iapply HΦ
      itrivial
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
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
    (γm : GName) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ echoInvs γm ∗ ⌜addrOk srvAddr = true⌝ ∗
        globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! Call)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hinvs, #Hplan, #Heof, #Hed⟩
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
    wp_apply wp_CallOne wp_Dial wp_ReadFull wp_Write wp_Close γm eof ed (W8 1) $$ []
    · iframe Hinvs Hplan Heof Hed
    (try wp_auto)
    wp_apply (sync.join.WaitGroup.wp_Done_of wp_Done iprop(True) wg_ptr) $$ [Hd1]
    · iframe Hd1
    itrivial
  (try wp_auto)
  wp_apply wp_fork $$ [Hd2]
  · (try wp_auto)
    wp_apply wp_CallOne wp_Dial wp_ReadFull wp_Write wp_Close γm eof ed (W8 2) $$ []
    · iframe Hinvs Hplan Heof Hed
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

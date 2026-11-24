/-
The proofs of `examples/net/shutdown`'s functions, over the specs of `net` and `wire`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `acceptLoop`: `Accept`s through the listener's invariant (`loop_accept_au`), each accepted
  connection's end closed (`acc_close_au`, its direction from `downInv`), until a failure.
* `readLoop`: `Read`s of the dialer's end through its invariant and `downInv` (`reader_read_au`),
  until an error.
* `closeConn`: the first `Close` (`first_close_au`: the end is closed after it), then a `Write`,
  a `Read` and a second `Close`, each of which fails on the closed end (`closed_write_acc`, the
  `Write`'s per-step accessor over the writer predicate `closedW`; `closed_read_au`,
  `closed_close_au`), so none of the panics is reached. The `Write` of one byte ends with an error:
  its result is `none` only once every byte is written (`net.Conn.Write.spec`), and its first step,
  on the closed end, fails with `closed`.
* `Run`: `Listen` (of `Addr` itself, `listenAt_self`, from the plan's entry in the network's ghost
  state), the listener's invariant (`lisInv_alloc`), `acceptLoop` forked, the dial
  (`wire.dial_au`, the deposit `shut_deposit`), the end's invariant (`endInv_alloc`),
  `readLoop` forked and `closeConn`; then the listener's `Close` (`lis_close_au`) and the last
  `Accept`, which fails since the listener is closed (`closed_accept_au`).

Each `err != nil` check follows from the failure's error being a non-nil `*OpError`
(`net.resErr_netErr`), whatever its kind; `Read` and `Write` take `poll.ErrDeadlineExceeded`'s
value (`wire.ed_of_poll`, from `internal/poll`'s initialization; `io.EOF`'s from `io`'s,
`eof_init`).

The node's command (`cmd/node`, whose `main` calls `Run`) is proved in `cmd/node/Main.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.shutdown.Defs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Net.Spec.net.Conn__Read
public import Net.Spec.net.Conn__Write
public import Net.Spec.net.Conn__Close
public import Net.Spec.net.Dial
public import Net.Spec.net.Listen
public import Net.Spec.net.Listener__Accept
public import Net.Spec.net.Listener__Close
public import Perennial.Proof.io
public import Net.Proof.net.AtAddr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv)

namespace github_com.mit_pdos.etcd_grove.examples.net.shutdown

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.shutdown

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : shutdown.Assumptions]
variable [go.BasicIntoValInj]

/-- `lisInv_alloc`, its update under a node's invariants. -/
theorem lisInv_alloc' (l : w64) :
    netLis (extLocalGS netExt (L := hG.goose_localGS)) l addr true ={⊤}=∗
      ∃ γo, inv lisN (lisInv (G (GF := GF)) (extLocalGS netExt (L := hG.goose_localGS)) l γo) ∗
        half G γo true :=
  lisInv_alloc _ l

/-- `endInv_alloc`, its update under a node's invariants. -/
theorem endInv_alloc' (cn : Nat) :
    netFresh (G (GF := GF)) cn false ={⊤}=∗ ∃ γc, inv endN (endInv G cn γc) ∗
      half G γc false :=
  endInv_alloc cn

theorem wp_acceptLoop
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (li : GoInterface) (l : w64) (γo : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ net.isListener li l ∗
        netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l addr ∗
        inv addrN (addrInv addr (connProto (GF := GF) γm)) ∗ inv downN (downInv G γm) ∗
        inv lisN (lisInv G (extLocalGS netExt (L := hG.goose_localGS)) l γo) }}
      (App (Val (@! acceptLoop)) (Val #li))
    {{ RET #(); True }} := by
  unfold net.isListener
  wp_start as ⟨⟨%t, %x, %Ht, #Hlt⟩, #Hla, #Ha, #Hdown, #Hl⟩
  subst Ht
  wp_auto
  wp_for
  wp_apply (net.Listener.Accept.spec_addrOk wp_Accept) t l x addr (fun _ => iprop(True)) (fun cn => connProto γm cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hproto⟩ | ⟨%k, -, #Herr⟩)
  · iframe Hlt Hla
    iapply loop_accept_au γm _ l γo $$ Ha Hl
  · -- a connection: close it
    subst Herr
    unfold net.isConn
    icases Hc with ⟨%t', %la, %ra, %Hct, #Hca⟩
    subst Hct
    wp_auto
    wp_apply wp_Close t' cn true addr la ra (fun _ => iprop(True)) $$ [Hproto]
      as %err' ⟨%res', -, -⟩
    · iframe Hca
      unfold connProto
      icases Hproto with ⟨Hend, #Hreg⟩
      iapply acc_close_au γm cn _ $$ Hdown Hreg Hend
    (try wp_auto)
    wp_for_post
    iframe
  · -- a failure: return
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hn
    obtain ⟨pe, rfl⟩ := Hn.2 (by simp)
    wp_auto
    wp_for_post
    iapply HΦ
    itrivial

theorem wp_readLoop
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (γm : GName) (c : GoInterface) (cn : Nat) (γc : GName) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ net.isConn c cn false addr ∗
        inv downN (downInv (G (GF := GF)) γm) ∗ downReg G γm cn ∗
        inv endN (endInv G cn γc) ∗ globalAddr io.EOF ↦□ eof ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! readLoop)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn
  wp_start as ⟨⟨%t, %la, %ra, %Hct, #Hc⟩, #Hdown, #Hreg, #Hinv, #Heof, #Hed⟩
  subst Hct
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  ihave HI : (∃ bs : List w8, "Hbuf" ∷ buf ↦* bs : IProp GF) $$ [Hbuf]
  · iexists _
    iexact Hbuf
  wp_for HI
  wp_apply wp_Read t cn false addr la ra buf bs eof ed (fun _ => iprop(True)) $$ [Hbuf]
    as %k %err ⟨%r, %bs', -, Hbuf, -⟩
  · iframe Hc Hbuf Heof Hed
    simp only [Bool.not_false]
    iapply reader_read_au γm cn γc buf.len.toNat $$ Hdown Hreg Hinv
  cases err with
  | nil =>
    -- no error: read again
    wp_auto
    wp_for_post
    iframe
    iexists bs'
    iframe Hbuf
  | ok i =>
    -- an error: return
    wp_auto
    wp_for_post
    iapply HΦ
    itrivial

theorem wp_closeConn
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (c : GoInterface) (cn : Nat) (γc : GName) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ net.isConn c cn false addr ∗
        inv downN (downInv (G (GF := GF)) γm) ∗ downReg G γm cn ∗
        inv endN (endInv G cn γc) ∗ half G γc false ∗ globalAddr io.EOF ↦□ eof ∗
        globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! closeConn)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn
  wp_start as ⟨⟨%t, %la, %ra, %Hct, #Hc⟩, #Hdown, #Hreg, #Hinv, Hh, #Heof, #Hed⟩
  subst Hct
  wp_auto
  wp_apply wp_Close t cn false addr la ra (fun _ => half G γc true) $$ [Hh]
    as %err ⟨%res, Hh, -⟩
  · iframe Hc
    iapply first_close_au cn γc $$ Hinv Hh
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  -- the `Write` fails
  wp_apply wp_Write t cn false addr la ra buf _ (DFrac.own 1) ed (closedW γc) $$ [Hbuf Hh]
    as %n %err ⟨%w, %resw, Hw, Hbuf, %Hn, #Herr⟩
  · iframe Hc Hbuf Hed
    isplitl [Hh]
    · unfold closedW
      iframe Hh
      ipureintro; exact Or.inl ⟨rfl, rfl⟩
    iapply closed_write_acc cn γc _ $$ Hinv
  unfold closedW
  icases Hw with ⟨Hh, %Hres⟩
  -- no step succeeds on the closed end, and the one byte is not written without one
  replace Hres : resw = some .closed := by
    rcases Hres with ⟨rfl, rfl⟩ | h
    · exact absurd (Hn.2.2.1 rfl) (by simp)
    · exact h
  subst Hres
  icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
  obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
  wp_auto
  -- the `Read` fails
  wp_apply wp_Read t cn false addr la ra buf _ eof ed
      (fun r => iprop(half G γc true ∗ ⌜r = .err .closed⌝)) $$ [Hbuf Hh]
    as %k' %err' ⟨%r, %bs', ⟨Hh, %Hr⟩, Hbuf, %Hout, Herr'⟩
  · iframe Hc Hbuf Heof Hed
    simp only [Bool.not_false]
    iapply closed_read_au γm cn γc buf.len.toNat $$ Hdown Hreg Hinv Hh
  subst Hr
  iunfold net.ReadErr at Herr'
  icases net.resErr_netErr (some .closed) go!"read" la ra (some ed) (· = go!"read") err'
    $$ Herr' with %Hne'
  obtain ⟨pe', rfl⟩ := Hne'.2 (by simp)
  wp_auto
  -- the second `Close` fails
  wp_apply wp_Close t cn false addr la ra
      (fun res => iprop(half G γc true ∗ ⌜res = some .closed⌝)) $$ [Hh]
    as %err'' ⟨%res'', ⟨Hh, %Hres⟩, #Herr''⟩
  · iframe Hc
    iapply closed_close_au cn γc $$ Hinv Hh
  subst Hres
  icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr'' with %Hne''
  obtain ⟨pe'', rfl⟩ := Hne''.2 (by simp)
  wp_auto
  iapply HΦ
  itrivial

theorem wp_Run
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_LClose : net.Listener.Close.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (γm : GName) (eof ed : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ inv addrN (addrInv addr (connProto (GF := GF) γm)) ∗
        inv downN (downInv G γm) ∗
        ⌜addrOk addr = true⌝ ∗
        globalAddr io.EOF ↦□ eof ∗ globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed }}
      (App (Val (@! Run)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Ha, #Hdown, %Hpl, #Heof, #Hed⟩
  (try wp_auto)
  wp_apply (net.Listen.spec_addrOk wp_Listen) go!"tcp" net.tcpNet_tcp addr $$ []
    as %li %err (⟨%Herr, %l, #Hli, Hlis, #Hla⟩ | ⟨%x, -, #Herr⟩)
  · iframe %Hpl
    iapply wire.listen_au addrN addr _ $$ Ha
  · -- listening
    subst Herr
    imod lisInv_alloc' l $$ Hlis with ⟨%γo, #Hl, Ho⟩
    iunfold net.isListener at Hli
    icases Hli with ⟨%t, %x, %Ht, #Hlt⟩
    subst Ht
    wp_auto
    wp_apply wp_fork $$ []
    · wp_apply wp_acceptLoop wp_Accept wp_Close γm _ l γo $$ []
      · iframe Ha Hdown Hl Hla
        unfold net.isListener
        iexists t, x
        iframe Hlt
        ipureintro; rfl
      itrivial
    (try wp_auto)
    wp_apply wp_Dial go!"tcp" net.tcpNet_tcp addr iprop(True)
        (fun cn => iprop(netFresh G cn false ∗ downReg G γm cn)) $$ []
      as %c %err (⟨%Herr, %cn, #Hc, ⟨Hd, #Hreg⟩⟩ | ⟨-, %x', -, #Herr⟩)
    · iframe %Hpl
      isplit
      · itrivial
      · iapply wire.dial_au addrN addr (connProto γm) (downReg G γm) $$ Ha
        iintro %cn #Hat Ha'
        iapply shut_deposit γm cn $$ Hdown Ha'
    · -- dialed: the reader, then the closes
      subst Herr
      imod endInv_alloc' cn $$ Hd with ⟨%γc, #He, Hh⟩
      wp_auto
      wp_apply wp_fork $$ []
      · wp_apply wp_readLoop wp_Read γm c cn γc eof ed $$ []
        · iframe Hc Hdown Hreg He Heof Hed
        itrivial
      (try wp_auto)
      wp_apply wp_closeConn wp_Read wp_Write wp_Close γm c cn γc eof ed $$ [Hh]
      · iframe Hc Hdown Hreg He Hh Heof Hed
      (try wp_auto)
      wp_apply wp_LClose t l x addr (fun _ => half G γo false) $$ [Ho] as %e1 ⟨%res1, Ho, -⟩
      · iframe Hlt
        isplitr
        · iapply netLisAt_on _ l addr $$ Hla
        iapply lis_close_au _ l γo $$ Hl Ho
      (try wp_auto)
      wp_apply (net.Listener.Accept.spec_addrOk wp_Accept) t l x addr (fun _ => iprop(True)) (fun _ => iprop(False)) $$ [Ho]
        as %c2 %e2 (⟨%He2, %cn2, -, Hf⟩ | ⟨%k2, -, #He2⟩)
      · iframe Hlt Hla
        iapply closed_accept_au γm _ l γo $$ Ha Hl Ho
      · icases Hf with ⟨⟩
      · icases net.resErr_netErr _ _ _ _ _ _ _ $$ He2 with %Hn
        obtain ⟨pe, rfl⟩ := Hn.2 (by simp)
        wp_auto
        iapply HΦ
        itrivial
    · -- not dialed: the listener's close
      icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hn
      obtain ⟨pe, rfl⟩ := Hn.2 (by simp)
      wp_auto
      wp_apply wp_LClose t l x addr (fun _ => half G γo false) $$ [Ho] as %e1 ⟨%res1, Ho, -⟩
      · iframe Hlt
        isplitr
        · iapply netLisAt_on _ l addr $$ Hla
        iapply lis_close_au _ l γo $$ Hl Ho
      (try wp_auto)
      wp_apply (net.Listener.Accept.spec_addrOk wp_Accept) t l x addr (fun _ => iprop(True)) (fun _ => iprop(False)) $$ [Ho]
        as %c2 %e2 (⟨%He2, %cn2, -, Hf⟩ | ⟨%k2, -, #He2⟩)
      · iframe Hlt Hla
        iapply closed_accept_au γm _ l γo $$ Ha Hl Ho
      · icases Hf with ⟨⟩
      · icases net.resErr_netErr _ _ _ _ _ _ _ $$ He2 with %Hn'
        obtain ⟨pe', rfl⟩ := Hn'.2 (by simp)
        wp_auto
        iapply HΦ
        itrivial
  · -- not listening: return
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hn
    obtain ⟨pe, rfl⟩ := Hn.2 (by simp)
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

end github_com.mit_pdos.etcd_grove.examples.net.shutdown
end Perennial

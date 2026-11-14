/-
The proofs of `examples/net/shutdown`'s functions, over the specs of `net` and `wire`
(hypotheses, linked in `Results.lean`) and the protocol of `Defs.lean`:

* `acceptLoop`: `Accept`s through the listener's invariant (`loop_accept_au`), each accepted
  connection's fresh end closed (`wire.owned_close_drop`), until a failure.
* `readLoop`: `Read`s of the dialer's end through its invariant (`reader_read_au`), until an error.
* `closeConn`: the first `Close` (`first_close_au`: the end is closed after it), then a `Write`,
  a `Read` and a second `Close`, each of which fails on the closed end (`closed_write_au`,
  `closed_read_au`, `closed_close_au`), so none of the panics is reached.
* `Run`: `Listen`, the listener's invariant (`lisInv_alloc`), `acceptLoop` forked, the dial
  (`wire.dial_au`, the deposit the acceptor's fresh end), the end's invariant (`endInv_alloc`),
  `readLoop` forked and `closeConn`; then the listener's `Close` (`lis_close_au`) and the last
  `Accept`, which fails since the listener is closed (`closed_accept_au`).
* `Node`: `Run`, then `wire.Forever`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.shutdown.Defs
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.ReadFull
public import NetTcp.Spec.github_com.mit_pdos.etcd_grove.examples.net.wire.Forever
public import NetTcp.Spec.net.Conn__Read
public import NetTcp.Spec.net.Conn__Write
public import NetTcp.Spec.net.Conn__Close
public import NetTcp.Spec.net.Dial
public import NetTcp.Spec.net.Listen
public import NetTcp.Spec.net.Listener__Accept
public import NetTcp.Spec.net.Listener__Close
public import Perennial.Proof.io

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap)

namespace github_com.mit_pdos.etcd_grove.examples.net.shutdown

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.net.shutdown

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : shutdown.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- `lisInv_alloc`, its update under a node's invariants. -/
theorem lisInv_alloc' (l : w64) :
    tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l addr true ={⊤}=∗
      ∃ γo, inv lisN (lisInv (G (GF := GF)) (extLocalGS tcpExt (L := hG.goose_localGS)) l γo) ∗
        half G γo true :=
  lisInv_alloc _ l

/-- `endInv_alloc`, its update under a node's invariants. -/
theorem endInv_alloc' (cn : Nat) :
    tcpFreshEnd (G (GF := GF)) cn false ={⊤}=∗ ∃ γc, inv endN (endInv G cn γc) ∗
      half G γc false :=
  endInv_alloc cn

theorem wp_acceptLoop
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (li : GoInterface) (l : w64) (γo : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ net.isListener li l ∗
        tcpLisAt (extLocalGS tcpExt (L := hG.goose_localGS)) l addr ∗
        inv addrN (addrInv addr (connProto (GF := GF))) ∗
        inv lisN (lisInv G (extLocalGS tcpExt (L := hG.goose_localGS)) l γo) }}
      (App (Val (@! acceptLoop)) (Val #li))
    {{ RET #(); True }} := by
  unfold net.isListener
  wp_start as ⟨⟨%t, %Ht, #Hlt⟩, #Hla, #Ha, #Hl⟩
  subst Ht
  wp_auto
  wp_for
  wp_apply wp_Accept t l addr iprop(True) (fun cn => connProto cn) $$ []
    as %c %err (⟨%Herr, %cn, #Hc, Hproto⟩ | ⟨%Herr, -⟩)
  · iframe Hlt Hla
    iapply loop_accept_au _ l γo $$ Ha Hl
  · -- a connection: close it
    subst Herr
    unfold net.isConn
    icases Hc with ⟨%t', %Hct, #Hca⟩
    subst Hct
    wp_auto
    wp_apply wp_Close t' cn true addr (fun _ => iprop(True)) $$ [Hproto] as %err' ⟨%ok', -, -⟩
    · iframe Hca
      unfold connProto tcpFreshEnd
      icases Hproto with ⟨Hend, Hout⟩
      iapply wire.owned_close_drop cn true _ _ _ false $$ Hend Hout
    (try wp_auto)
    wp_for_post
    iframe
  · -- a failure: return
    obtain ⟨pe, rfl⟩ := Herr
    wp_auto
    wp_for_post
    iapply HΦ
    itrivial

theorem wp_readLoop
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (c : GoInterface) (cn : Nat) (γc : GName) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ net.isConn c cn false addr ∗
        inv endN (endInv (G (GF := GF)) cn γc) ∗ globalAddr io.EOF ↦□ eof }}
      (App (Val (@! readLoop)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn
  wp_start as ⟨⟨%t, %Hct, #Hc⟩, #Hinv, #Heof⟩
  subst Hct
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  ihave HI : (∃ bs : List w8, "Hbuf" ∷ buf ↦* bs : IProp GF) $$ [Hbuf]
  · iexists _
    iexact Hbuf
  wp_for HI
  wp_apply wp_Read t cn false addr buf bs eof (fun _ => iprop(True)) $$ [Hbuf]
    as %k %err ⟨%bs1, %code, %bs', -, Hbuf, -⟩
  · iframe Hc Hbuf Heof
    iapply reader_read_au cn γc buf.len $$ Hinv
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
    (c : GoInterface) (cn : Nat) (γc : GName) (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ net.isConn c cn false addr ∗
        inv endN (endInv (G (GF := GF)) cn γc) ∗ half G γc false ∗ globalAddr io.EOF ↦□ eof }}
      (App (Val (@! closeConn)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn
  wp_start as ⟨⟨%t, %Hct, #Hc⟩, #Hinv, Hh, #Heof⟩
  subst Hct
  wp_auto
  wp_apply wp_Close t cn false addr (fun _ => half G γc true) $$ [Hh] as %err ⟨%ok, Hh, -⟩
  · iframe Hc
    iapply first_close_au cn γc $$ Hinv Hh
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  -- the `Write` fails
  wp_apply wp_Write t cn false addr buf _ (DFrac.own 1)
      (fun _ ok => iprop(half G γc true ∗ ⌜ok = false⌝)) $$ [Hbuf Hh]
    as %n %err ⟨%k, %okw, ⟨Hh, %Hok⟩, Hbuf, %Hn⟩
  · iframe Hc Hbuf
    iapply closed_write_au cn γc _ $$ Hinv Hh
  subst Hok
  obtain ⟨-, -, Herr⟩ := Hn
  obtain ⟨pe, rfl⟩ := Herr rfl
  wp_auto
  -- the `Read` fails
  wp_apply wp_Read t cn false addr buf _ eof
      (fun res => iprop(half G γc true ∗ ⌜res = readRes [] 2⌝)) $$ [Hbuf Hh]
    as %k' %err' ⟨%bs1, %code, %bs', ⟨Hh, %Hr⟩, Hbuf, %Hout⟩
  · iframe Hc Hbuf Heof
    iapply closed_read_au cn γc buf.len $$ Hinv Hh
  obtain ⟨rfl, rfl⟩ := wire.readRes_inj Hr
  rcases Hout with ⟨h0, -⟩ | ⟨h1, -⟩ | ⟨-, -, -, ⟨pe', rfl⟩, -⟩
  · cases h0
  · cases h1
  wp_auto
  -- the second `Close` fails
  wp_apply wp_Close t cn false addr (fun ok => iprop(half G γc true ∗ ⌜ok = false⌝)) $$ [Hh]
    as %err'' ⟨%ok'', ⟨Hh, %Hok⟩, %Herr⟩
  · iframe Hc
    iapply closed_close_au cn γc $$ Hinv Hh
  subst Hok
  obtain ⟨pe'', rfl⟩ := Herr.2 rfl
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
    (eof : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ inv addrN (addrInv addr (connProto (GF := GF))) ∗
        tcpPlan G addr (extLocalGS tcpExt (L := hG.goose_localGS)).host ∗
        globalAddr io.EOF ↦□ eof }}
      (App (Val (@! Run)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Ha, #Hplan, #Heof⟩
  (try wp_auto)
  wp_apply wp_Listen addr $$ Hplan as %li %err (⟨%Herr, %l, #Hli, Hlis, #Hla⟩ | %Herr)
  · -- listening
    subst Herr
    imod lisInv_alloc' l $$ Hlis with ⟨%γo, #Hl, Ho⟩
    iunfold net.isListener at Hli
    icases Hli with ⟨%t, %Ht, #Hlt⟩
    subst Ht
    wp_auto
    wp_apply wp_fork $$ []
    · wp_apply wp_acceptLoop wp_Accept wp_Close _ l γo $$ []
      · iframe Ha Hl Hla
        unfold net.isListener
        iexists t
        iframe Hlt
        ipureintro; rfl
      itrivial
    (try wp_auto)
    wp_apply wp_Dial addr _ iprop(True) (fun cn => iprop(tcpFreshEnd G cn false ∗ True)) $$ []
      as %c %err (⟨%Herr, %cn, #Hc, ⟨Hd, -⟩⟩ | ⟨%Herr, -⟩)
    · iframe Hplan
      isplit
      · itrivial
      · iapply wire.dial_au addrN addr connProto (fun _ => iprop(True)) $$ Ha
        iintro %cn #Hat Ha'
        imodintro
        unfold connProto
        iframe Ha'
    · -- dialed: the reader, then the closes
      subst Herr
      imod endInv_alloc' cn $$ Hd with ⟨%γc, #He, Hh⟩
      wp_auto
      wp_apply wp_fork $$ []
      · wp_apply wp_readLoop wp_Read c cn γc eof $$ []
        · iframe Hc He Heof
        itrivial
      (try wp_auto)
      wp_apply wp_closeConn wp_Read wp_Write wp_Close c cn γc eof $$ [Hh]
      · iframe Hc He Hh Heof
      (try wp_auto)
      wp_apply wp_LClose t l addr (fun _ => half G γo false) $$ [Ho] as %e1 ⟨%o, Ho, -⟩
      · iframe Hlt Hla
        iapply lis_close_au _ l γo $$ Hl Ho
      (try wp_auto)
      wp_apply wp_Accept t l addr iprop(True) (fun _ => iprop(False)) $$ [Ho]
        as %c2 %e2 (⟨%He2, %cn2, -, Hf⟩ | ⟨%He2, -⟩)
      · iframe Hlt Hla
        iapply closed_accept_au _ l γo $$ Ha Hl Ho
      · icases Hf with ⟨⟩
      · obtain ⟨pe, rfl⟩ := He2
        wp_auto
        iapply HΦ
        itrivial
    · -- not dialed: the listener's close
      obtain ⟨pe, rfl⟩ := Herr
      wp_auto
      wp_apply wp_LClose t l addr (fun _ => half G γo false) $$ [Ho] as %e1 ⟨%o, Ho, -⟩
      · iframe Hlt Hla
        iapply lis_close_au _ l γo $$ Hl Ho
      (try wp_auto)
      wp_apply wp_Accept t l addr iprop(True) (fun _ => iprop(False)) $$ [Ho]
        as %c2 %e2 (⟨%He2, %cn2, -, Hf⟩ | ⟨%He2, -⟩)
      · iframe Hlt Hla
        iapply closed_accept_au _ l γo $$ Ha Hl Ho
      · icases Hf with ⟨⟩
      · obtain ⟨pe', rfl⟩ := He2
        wp_auto
        iapply HΦ
        itrivial
  · -- not listening: return
    obtain ⟨pe, rfl⟩ := Herr
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

theorem wp_Node
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_LClose : net.Listener.Close.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Forever : wire.Forever.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ inv addrN (addrInv addr (connProto (GF := GF))) ∗
        tcpPlan G addr (extLocalGS tcpExt (L := hG.goose_localGS)).host }}
      (App (Val (@! Node)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Ha, #Hplan⟩
  icases eof_init $$ Hpkg with ⟨%eof, #Heof⟩
  (try wp_auto)
  wp_apply wp_Run wp_Listen wp_Accept wp_LClose wp_Dial wp_Read wp_Write wp_Close eof $$ []
  · iframe Ha Hplan Heof
  (try wp_auto)
  wp_apply wp_Forever as ⟨⟩

end proof

end github_com.mit_pdos.etcd_grove.examples.net.shutdown
end Perennial

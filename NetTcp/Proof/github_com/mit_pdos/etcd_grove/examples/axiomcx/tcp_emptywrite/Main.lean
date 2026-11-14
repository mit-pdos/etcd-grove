/-
The counterexample of `notes/axiom-review/tcp-semantics.md`: `examples/axiomcx/tcp-emptywrite`'s
`Main` dials its own listener, sets a deadline that has passed (`time.Now()`), and writes no bytes,
panicking if the `Write` fails. On Linux 7.0 with Go 1.27.3 it panics on every run (the `Write`
returns a timeout: `(*poll.FD).Write` checks the deadline before `write(2)`; its test,
`TestMainPanics`). Under the TCP extension's semantics it never panics: `Main.wp_main` below, from
the specs of `net` (`NetTcp/Spec/net/`, proved from the trusted models and the extension) and
`time.Now`'s.

The semantic step that excludes Go's outcome is `WriteOutcome` (`GooseLang/Ext/Tcp/Impl.lean`, D2):
on an end that is not closed, into a direction it has not shut, every failure writes fewer bytes
than asked (`k < bs.length`), which no count satisfies when `bs = []`; so an empty `Write` there
succeeds (`emptyWrite_ok`).
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_emptywrite.Base
public import NetTcp.Spec.net.Conn__Write
public import NetTcp.Spec.net.Conn__SetDeadline
public import NetTcp.Spec.net.Conn__Close
public import NetTcp.Spec.net.Dial
public import NetTcp.Spec.net.Listen
public import NetTcp.Spec.net.Listener__Close
public import Perennial.Spec.time.Now
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Addr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv)

namespace github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_emptywrite

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_emptywrite

/-- `Addr`. -/
abbrev addr : GoString := go!"127.0.0.1:7199"

/-- The namespace of `Addr`'s invariant. -/
def addrN : Namespace := nroot.@"tcp_emptywrite_addr"

/-- The semantic step: an empty `Write` on an end that is not closed, into a direction it has not
shut, succeeds (whatever the deadlines, and even into a broken direction). Go returns an error
there with an expired write deadline, or after a reset. -/
theorem emptyWrite_ok {st : TcpEnd} {d d' : TcpDir} {bs : List w8} {k : Nat} {ok : Bool}
    (hc : st.closed = false) (hf : d.status ≠ .fin) (hbs : bs.length = 0)
    (h : WriteOutcome st d bs k ok d') : ok = true := by
  unfold WriteOutcome at h
  simp only [hc, Bool.false_or, decide_eq_true_eq, hf, ite_false, hbs] at h
  split at h
  · rcases h with ⟨(⟨-, h⟩ | ⟨h, -⟩), -⟩
    · exact h
    · omega
  · rcases h with ⟨-, h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩ <;> first | exact h | omega

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : tcp_emptywrite.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- An owned listener's close: the update of `net.Listener.Close`. -/
theorem lis_close_au (l : w64) :
    ⊢ tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l addr true -∗
      |={⊤,∅}=> ∃ o, tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l addr o ∗
        (tcpLis (extLocalGS tcpExt (L := hG.goose_localGS)) l addr false ={∅,⊤}=∗ True) := by
  iintro Hl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists true
  iframe Hl
  iintro -
  imod Hmask
  imodintro
  itrivial

/-- `Main` does not panic: the empty `Write` succeeds (`emptyWrite_ok`). The precondition: the
plan has `Addr` at this node's host, and `Addr`'s invariant (`wire.addrInv`, with no deposit). -/
theorem wp_Main
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_LClose : net.Listener.Close.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_SetDeadline : net.Conn.SetDeadline.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        tcpPlan G addr (extLocalGS tcpExt (L := hG.goose_localGS)).host ∗
        inv addrN (addrInv (GF := GF) addr (fun _ => iprop(True))) }}
      (App (Val (@! Main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hplan, #Ha⟩
  (try wp_auto)
  wp_apply wp_Listen addr $$ Hplan as %li %err (⟨%Herr, %l, #Hli, Hlis, #Hla⟩ | %Herr)
  · -- listening
    subst Herr
    iunfold net.isListener at Hli
    icases Hli with ⟨%t, %Ht, #Hlt⟩
    subst Ht
    wp_auto
    wp_apply wp_Dial addr _ iprop(True) (fun cn => iprop(tcpFresh G cn false ∗ True)) $$ []
      as %c %err (⟨%Herr, %cn, #Hc, ⟨Hd, -⟩⟩ | ⟨%Herr, -⟩)
    · iframe Hplan
      isplit
      · itrivial
      · iapply github_com.mit_pdos.etcd_grove.examples.net.wire.dial_au addrN addr (fun _ => iprop(True)) (fun _ => iprop(True)) $$ Ha
        iintro %cn - -
        imodintro
        isplit <;> itrivial
    · -- dialed
      subst Herr
      unfold net.isConn
      icases Hc with ⟨%t', %Hct, #Hca⟩
      subst Hct
      iunfold tcpFresh at Hd
      icases Hd with ⟨Hend, Hdir⟩
      wp_auto
      wp_apply wp_Now as %tm -
      wp_apply wp_SetDeadline t' cn false addr tm
          (fun _ => iprop(∃ st', tcpEnd G cn false st' ∗ ⌜st'.closed = false⌝)) $$ [Hend]
        as %e0 ⟨%ok0, ⟨%st1, Hend, %Hst1⟩, -⟩
      · iframe Hca
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hmask
        iexists TcpEnd.fresh
        iframe Hend
        iintro %ok %st' %Hout Hend
        imod Hmask
        imodintro
        iexists st'
        iframe Hend
        ipureintro
        unfold DeadlineOutcome at Hout
        simp only [TcpEnd.fresh] at Hout
        obtain ⟨-, rfl⟩ := Hout
        rfl
      (try wp_auto)
      wp_apply (wp_slice_make2 (V := w8) (W64 0)) as %buf ⟨Hbuf, -⟩
      · ipureintro; decide
      (try wp_auto)
      wp_apply wp_Write t' cn false addr buf _ (DFrac.own 1)
          (fun _ ok => iprop(⌜ok = true⌝ ∗ tcpEnd G cn false st1 ∗ ∃ d, tcpDir G cn false d))
          $$ [Hbuf Hend Hdir]
        as %n %err ⟨%k, %okw, ⟨%Hok, Hend, %d, Hdir⟩, Hbuf, %Hn⟩
      · iframe Hca Hbuf
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hmask
        iexists st1, TcpDir.fresh
        iframe Hend Hdir
        iintro %k %ok %d' %Hw Hend Hdir
        imod Hmask
        imodintro
        iframe Hend
        isplitl []
        · ipureintro
          exact emptyWrite_ok Hst1 (by simp [TcpDir.fresh]) (by simp) Hw
        · iexists d'
          iexact Hdir
      subst Hok
      obtain ⟨-, Hnil, -⟩ := Hn
      obtain rfl := Hnil rfl
      wp_auto
      wp_apply wp_Close t' cn false addr (fun _ => iprop(True)) $$ [Hend Hdir] as %e1 ⟨%ok1, -, -⟩
      · iframe Hca
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hmask
        iexists st1, d
        iframe Hend Hdir
        iintro %ok %st' %d' - - -
        imod Hmask
        imodintro
        itrivial
      (try wp_auto)
      wp_apply wp_LClose t l addr (fun _ => iprop(True)) $$ [Hlis] as %e2 ⟨%o, -, -⟩
      · iframe Hlt Hla
        iapply lis_close_au l $$ Hlis
      (try wp_auto)
      iapply HΦ
      itrivial
    · -- not dialed: close the listener
      obtain ⟨pe, rfl⟩ := Herr
      wp_auto
      wp_apply wp_LClose t l addr (fun _ => iprop(True)) $$ [Hlis] as %e2 ⟨%o, -, -⟩
      · iframe Hlt Hla
        iapply lis_close_au l $$ Hlis
      (try wp_auto)
      iapply HΦ
      itrivial
  · -- not listening: return
    obtain ⟨pe, rfl⟩ := Herr
    wp_auto
    iapply HΦ
    itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_emptywrite
end Perennial

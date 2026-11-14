/-
The counterexample of `notes/axiom-review/tcp-semantics.md`, v3: `examples/axiomcx/tcp-writedeadline`'s
`Main` listens at `Addr`, dials it and accepts; a second goroutine (`reader`) reads one byte at the
acceptor's end and, if it got one, sets the dialer's deadline to the present; `Main` writes 32 MiB at
the dialer's end and panics if the `Write`'s error is a timeout (`Timeout()`) whose `Err` is not an
`*os.SyscallError`. On Linux 7.0 with Go 1.27.3 it panics in about 99 runs of 100 (the blocked
`Write` returns `(n, os.ErrDeadlineExceeded)`, `0 < n < 32 MiB`: `TestMainPanics`,
`TestWriteDeadlineSetDuring`). Under the TCP extension's semantics it never panics (`wp_Main`).

The semantic step that excludes Go's outcome is `WriteOutcome` (`GooseLang/Ext/Tcp/Impl.lean`, D2):
a `Write` is one step, which may time out only if the end's write deadline is set at that step
(`write_noTimeout`). The reader's byte must have been appended by that step before the reader's
`Read` returned it (an empty direction gives no bytes: `read_empty`), and the deadline is set after
that `Read`, so at the `Write`'s step it was not set. The ghost argument (`raceInv`): the dialer's
end and its direction are in an invariant that is either *before the write* (the direction empty,
no write deadline, and the reader's token `γr` inside) or *after* (the writer's token `γw` inside,
and `γr` until the reader takes it). The `Write` holds `γw`, so it steps before; a `Read` that
returns a byte sees after and takes `γr`; the `SetDeadline`, holding `γr`, sees after.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_writedeadline.Base
public import NetTcp.Spec.net.Conn__Read
public import NetTcp.Spec.net.Conn__Write
public import NetTcp.Spec.net.Conn__SetDeadline
public import NetTcp.Spec.net.Dial
public import NetTcp.Spec.net.Listen
public import NetTcp.Spec.net.Listener__Accept
public import NetTcp.Spec.net.OpError__Timeout
public import Perennial.Spec.time.Now
public import Perennial.Proof.io
public import Perennial.Ghost.Token
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Addr

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G)

namespace github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_writedeadline

local notation "pkg" => pkg_id.github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_writedeadline

/-- `Addr`. -/
abbrev addr : GoString := go!"127.0.0.1:7197"

/-! ## The semantic steps -/

theorem readAvail_empty {st : TcpEnd} {d d' : TcpDir} {n : Nat} {r : ReadRes}
    (hd : d.bytes = []) (h : ReadAvail st d n r d') : (∀ bs, r ≠ .bytes bs) ∧ d'.bytes = [] := by
  unfold ReadAvail at h
  rcases h with ⟨k, hk1, -, hk, -, -⟩ | ⟨-, -, hr, hd'⟩ | ⟨-, -, hr, hd'⟩ | ⟨-, hr, hd'⟩ |
      ⟨-, hr, hd'⟩
  · rw [hd] at hk; simp at hk; omega
  all_goals
    refine ⟨fun bs h => ?_, ?_⟩
    · rw [hr] at h; cases h
    · rw [hd']; exact hd

/-- A `Read` of `n > 0` bytes from an empty direction returns no bytes, and leaves the direction
empty. -/
theorem read_empty {st : TcpEnd} {d d' : TcpDir} {n : Nat} {r : ReadRes}
    (hd : d.bytes = []) (hn : n ≠ 0) (h : ReadOutcome st d n r d') :
    (∀ bs, r ≠ .bytes bs) ∧ d'.bytes = [] := by
  unfold ReadOutcome at h
  split at h
  · obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun bs h => ?_, hd⟩
    cases h
  · rcases h with h | ⟨k, -, h⟩
    · exact readAvail_empty hd h
    · exact readAvail_empty (by simp [hd]) h

/-- The semantic step: a `Write` at an end whose write deadline is not set does not time out. -/
theorem write_noTimeout {st : TcpEnd} {d d' : TcpDir} {bs : List w8} {k : Nat}
    {res : Option TcpErr} (hw : st.wdl = false) (h : WriteOutcome st d bs k res d') :
    res ≠ some .timeout := by
  unfold WriteOutcome at h
  split at h
  · obtain ⟨-, rfl, -⟩ := h; intro h; cases h
  · split at h
    · obtain ⟨-, -, h | ⟨h, -⟩⟩ := h
      · rw [h]; intro h; cases h
      · rw [hw] at h; cases h
    · obtain ⟨-, ⟨-, rfl⟩ | ⟨-, h | h | ⟨h, -⟩⟩⟩ := h
      · intro h; cases h
      · rw [h]; intro h; cases h
      · rw [h]; intro h; cases h
      · rw [hw] at h; cases h
    · rcases h with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨h, -⟩ | ⟨-, rfl, -⟩
      · intro h; cases h
      · intro h; cases h
      · rw [hw] at h; cases h
      · intro h; cases h

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : tcp_writedeadline.Assumptions] [field_sem : net.FieldAssumptions]
variable [go.BasicIntoValInj]

/-- The namespace of the race's invariant. -/
def raceN : Namespace := nroot.@"tcp_writedeadline_race"

/-- The race's invariant, over the dialer's end of `cn` and its direction: before the `Write`'s
step (the direction empty, no write deadline; the reader's token `γr` inside), or after it (the
writer's token `γw` inside, with `γr` until the reader takes it, leaving its own `γx`). -/
def raceInv (cn : Nat) (γw γr γx : GName) : IProp GF :=
  iprop(∃ st d, tcpEnd (G (GF := GF)) cn false st ∗ tcpDir G cn false d ∗
    ((⌜d.bytes = [] ∧ st.wdl = false⌝ ∗ token γr) ∨ (token γw ∗ (token γr ∨ token γx))))

/-- The `Write`'s update: it does not time out (`write_noTimeout`). -/
theorem write_au (cn : Nat) (γw γr γx : GName) (bs : List w8) :
    ⊢ inv raceN (raceInv (GF := GF) cn γw γr γx) -∗ token γw -∗
      |={⊤,∅}=> ∃ st d, tcpEnd G cn false st ∗ tcpDir G cn false d ∗
        ∀ k res d', ⌜WriteOutcome st d bs k res d'⌝ -∗ tcpEnd G cn false st -∗
          tcpDir G cn false d' ={∅,⊤}=∗ ⌜res ≠ some .timeout⌝ := by
  iintro #Hinv Hw
  iinv Hinv with Hi Hclose
  unfold raceInv
  icases Hi with ⟨%st, %d, >Hend, >Hdir, (⟨>%Hb, >Hr⟩ | ⟨>Hw', -⟩)⟩
  · iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists st, d
    iframe Hend Hdir
    iintro %k %res %d' %Hwo Hend Hdir
    imod Hmask
    imod Hclose $$ [Hend Hdir Hw Hr] with -
    · inext
      iexists st, d'
      iframe Hend Hdir
      iright
      iframe Hw
      ileft
      iexact Hr
    imodintro
    ipureintro
    exact write_noTimeout Hb.2 Hwo
  · iexfalso
    iapply token_exclusive γw $$ Hw Hw'

/-- The reader's `Read`: a byte only after the `Write`'s step, and then the reader takes `γr`. -/
theorem read_au (cn : Nat) (γw γr γx : GName) (n : Nat) (hn : n ≠ 0) :
    ⊢ inv raceN (raceInv (GF := GF) cn γw γr γx) -∗ token γx -∗
      tcpEnd G cn true TcpEnd.fresh -∗
      |={⊤,∅}=> ∃ st d, tcpEnd G cn true st ∗ tcpDir G cn false d ∗
        ∀ r d', ⌜ReadOutcome st d n r d' ∧ r ≠ .wait⌝ -∗ tcpEnd G cn true st -∗
          tcpDir G cn false d' ={∅,⊤}=∗
            iprop(tcpEnd G cn true TcpEnd.fresh ∗ (⌜∀ bs, r ≠ .bytes bs⌝ ∨ token γr)) := by
  iintro #Hinv Hx He
  iinv Hinv with Hi Hclose
  unfold raceInv
  icases Hi with ⟨%st, %d, >Hend, >Hdir, (⟨>%Hb, >Hr⟩ | ⟨>Hw, >(Hr | Hx')⟩)⟩
  · -- before the write: the direction is empty, no byte
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists TcpEnd.fresh, d
    iframe He Hdir
    iintro %r %d' %Hro He Hdir
    imod Hmask
    have Hre := read_empty Hb.1 hn Hro.1
    imod Hclose $$ [Hend Hdir Hr] with -
    · inext
      iexists st, d'
      iframe Hend Hdir
      ileft
      iframe Hr
      ipureintro; exact ⟨Hre.2, Hb.2⟩
    imodintro
    iframe He
    ileft
    ipureintro; exact Hre.1
  · -- after the write: take `γr`
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists TcpEnd.fresh, d
    iframe He Hdir
    iintro %r %d' %Hro He Hdir
    imod Hmask
    imod Hclose $$ [Hend Hdir Hw Hx] with -
    · inext
      iexists st, d'
      iframe Hend Hdir
      iright
      iframe Hw
      iright
      iexact Hx
    imodintro
    iframe He
    iright
    iexact Hr
  · iexfalso
    iapply token_exclusive γx $$ Hx Hx'

/-- The reader's `SetDeadline`, holding `γr`: after the `Write`'s step. -/
theorem deadline_au (cn : Nat) (γw γr γx : GName) (set : Bool) :
    ⊢ inv raceN (raceInv (GF := GF) cn γw γr γx) -∗ token γr -∗
      |={⊤,∅}=> ∃ st, tcpEnd G cn false st ∗
        ∀ res st', ⌜DeadlineOutcome st (W64 0) set res st'⌝ -∗
          tcpEnd G cn false st' ={∅,⊤}=∗ True := by
  iintro #Hinv Hr
  iinv Hinv with Hi Hclose
  unfold raceInv
  icases Hi with ⟨%st, %d, >Hend, >Hdir, (⟨-, >Hr'⟩ | ⟨>Hw, >Hrx⟩)⟩
  · iexfalso
    iapply token_exclusive γr $$ Hr Hr'
  · iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists st
    iframe Hend
    iintro %res %st' - Hend
    imod Hmask
    imod Hclose $$ [Hend Hdir Hw Hrx] with -
    · inext
      iexists st', d
      iframe Hend Hdir
      iright
      iframe Hw Hrx
    imodintro
    itrivial

/-- `internal/poll`'s package fact, from its `isPkgInit`. -/
theorem poll_isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.internal.poll ⊢
      iprop((∃ e : GoInterface, globalAddr internal.poll.ErrNoDeadline ↦□ e) ∗
        (∃ e : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ e)) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.internal.poll

/-- `poll.ErrDeadlineExceeded`'s value, from the package's initialization. -/
theorem ed_init :
    isPkgInit (PROP := IProp GF) pkg ⊢ ∃ ed : GoInterface,
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  iintro #Hpkg
  ihave #Hp : (isPkgInit (PROP := IProp GF) pkg_id.internal.poll) $$ []
  · iPkgInit
  ihave Hf := poll_isInit_access $$ Hp
  icases Hf with ⟨-, ⟨%ed, #Hed⟩⟩
  iexists ed
  iexact Hed

/-- `io.EOF`'s value, a non-nil error, from the package's initialization. -/
theorem eof_init :
    isPkgInit (PROP := IProp GF) pkg ⊢ ∃ x : Loc,
      globalAddr io.EOF ↦□ interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x := by
  iintro #Hpkg
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  ihave #Hn := io.eof_of_init $$ Hio
  isimp only [_root_.Perennial.errors.newVar] at Hn
  icases Hn with ⟨%eofl, #Heof, -⟩
  iexists eofl
  iexact Heof

theorem wp_reader
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_SetDeadline : net.Conn.SetDeadline.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (a c : GoInterface) (cn : Nat) (γw γr γx : GName) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ net.isConn a cn true addr ∗ net.isConn c cn false addr ∗
        inv raceN (raceInv cn γw γr γx) ∗ token γx ∗ tcpEnd G cn true TcpEnd.fresh }}
      (App (App (Val (@! reader)) (Val #a)) (Val #c))
    {{ RET #(); True }} := by
  unfold net.isConn
  wp_start as ⟨⟨%ta, %laa, %raa, %Hat, #Ha⟩, ⟨%tc, %lac, %rac, %Hct, #Hc⟩, #Hinv, Hx, He⟩
  subst Hat Hct
  icases eof_init $$ [] with ⟨%eofl, #Heof⟩
  · iPkgInit
  icases ed_init $$ [] with ⟨%ed, #Hed⟩
  · iPkgInit
  wp_auto
  wp_apply (wp_slice_make2 (V := w8) (W64 1)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  ihave %Hlen := ownSlice_len $$ Hbuf
  have hn : buf.len.toNat ≠ 0 := by
    obtain ⟨Hl, -⟩ := Hlen
    simp only [List.length_replicate] at Hl
    word
  wp_apply wp_Read ta cn true addr laa raa buf _
      (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #eofl) ed
      (fun r => iprop(tcpEnd G cn true TcpEnd.fresh ∗ (⌜∀ bs, r ≠ .bytes bs⌝ ∨ token γr)))
      $$ [Hbuf Hx He]
    as %k %err ⟨%r, %bs', ⟨He, HQ⟩, Hbuf, %Hout, Herr⟩
  · iframe Ha Hbuf Heof Hed
    simp only [Bool.not_true]
    iapply read_au cn γw γr γx _ hn $$ Hinv Hx He
  cases r with
  | bytes bs =>
    -- a byte: after the write's step
    iunfold net.ReadErr at Herr
    icases Herr with %Herr
    subst Herr
    icases HQ with (%Hno | Hr)
    · exact absurd rfl (Hno bs)
    wp_auto
    wp_apply wp_Now as %tm -
    wp_apply wp_SetDeadline tc cn false addr lac rac tm (fun _ => iprop(True)) $$ [Hr]
      as %e0 ⟨%res0, -, -⟩
    · iframe Hc
      iapply deadline_au cn γw γr γx _ $$ Hinv Hr
    (try wp_auto)
    iapply HΦ
    itrivial
  | eof =>
    iunfold net.ReadErr at Herr
    icases Herr with %Herr
    subst Herr
    wp_auto
    iapply HΦ
    itrivial
  | err e =>
    iunfold net.ReadErr at Herr
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    iapply HΦ
    itrivial
  | wait =>
    iunfold net.ReadErr at Herr
    icases Herr with ⟨⟩

/-- `Main` does not panic: the `Write` never times out (`write_au`), so its error's `Err` is an
`*os.SyscallError` or `net.ErrClosed`, whose `Timeout()` is `false`. The precondition: the plan
has `Addr` at this node's host, and `Addr`'s pending set, empty (the network's start resources). -/
theorem wp_Main
    (wp_Listen : net.Listen.spec (GF := GF) (hG := hG))
    (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Accept : net.Listener.Accept.spec (GF := GF) (hG := hG))
    (wp_Read : net.Conn.Read.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_SetDeadline : net.Conn.SetDeadline.spec (GF := GF) (hG := hG))
    (wp_Timeout : net.OpError.Timeout.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        tcpPlan G addr (extLocalGS tcpExt (L := hG.goose_localGS)).host ∗
        ⌜(G (GF := GF)).plan !! addr = some (extLocalGS tcpExt (L := hG.goose_localGS)).host⌝ ∗
        tcpPend G addr ∅ }}
      (App (Val (@! Main)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hplan, %Hpl, Hpend⟩
  icases ed_init $$ [] with ⟨%ed, #Hed⟩
  · iPkgInit
  (try wp_auto)
  wp_apply wp_Listen addr addr $$ []
    as %li %err (⟨%Herr, %l, #Hli, Hlis, #Hla⟩ | ⟨%x, -, #Herr⟩)
  · ipureintro; exact listenAt_self Hpl
  rotate_left
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    iapply HΦ
    itrivial
  subst Herr
  iunfold net.isListener at Hli
  icases Hli with ⟨%t, %x, %Ht, #Hlt⟩
  subst Ht
  wp_auto
  wp_apply wp_Dial addr _ iprop(True)
      (fun cn => iprop(tcpPend G addr (∅ ∪ {[cn]}) ∗ tcpFresh G cn false ∗ tcpFresh G cn true))
      $$ [Hpend]
    as %c %err (⟨%Herr, %cn, #Hc, ⟨Hpend, Hd, Hfa⟩⟩ | ⟨-, %x', -, #Herr⟩)
  · iframe Hplan
    isplit
    · itrivial
    · iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      iexists ∅
      iframe Hpend
      iintro %cn - Hpend - Hfa
      isplit
      · iintro Hd
        imod Hmask
        imodintro
        iframe Hpend Hd Hfa
      · iintro - -
        imod Hmask
        imodintro
        itrivial
  rotate_left
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    iapply HΦ
    itrivial
  subst Herr
  wp_auto
  wp_apply wp_Accept t l x addr (fun _ => iprop(True)) (fun cn' => iprop(⌜cn = cn'⌝))
      $$ [Hlis Hpend]
    as %a %err (⟨%Herr, %cn', #Ha, %Heq⟩ | ⟨%k, -, #Herr⟩)
  · iframe Hlt Hla
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists true, (∅ ∪ {[cn]})
    iframe Hlis Hpend
    isplit
    · iintro - -
      imod Hmask
      imodintro
      itrivial
    · iintro - %cn' %Hin - - -
      imod Hmask
      imodintro
      ipureintro
      rcases (GMap.elem_of_union _ _ _).1 Hin with h | h
      · exact absurd h (GMap.not_elem_of_empty _)
      · exact ((GMap.elem_of_singleton _ _).1 h).symm
  rotate_left
  · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
    obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
    wp_auto
    iapply HΦ
    itrivial
  subst Herr Heq
  -- the race's invariant
  imod token_alloc (GF := GF) with ⟨%γw, Hw⟩
  imod token_alloc (GF := GF) with ⟨%γr, Hr⟩
  imod token_alloc (GF := GF) with ⟨%γx, Hx⟩
  iunfold tcpFresh at Hd Hfa
  icases Hd with ⟨Hend, Hdir⟩
  icases Hfa with ⟨Hea, -⟩
  imod inv_alloc raceN ⊤ (raceInv (GF := GF) cn γw γr γx) $$ [Hend Hdir Hr] with #Hinv
  · inext
    unfold raceInv
    iexists TcpEnd.fresh, TcpDir.fresh
    iframe Hend Hdir
    ileft
    iframe Hr
    ipureintro
    exact ⟨rfl, rfl⟩
  wp_auto
  wp_apply wp_fork $$ [Hx Hea]
  · wp_apply wp_reader wp_Read wp_SetDeadline wp_Now a c cn γw γr γx $$ [Hx Hea]
    · iframe Ha Hc Hinv Hx Hea
    itrivial
  (try wp_auto)
  iunfold net.isConn at Hc
  icases Hc with ⟨%tc, %lac, %rac, %Hct, #Hca⟩
  subst Hct
  wp_apply (wp_slice_make2 (V := w8) (W64 33554432)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply wp_Write tc cn false addr lac rac buf _ (DFrac.own 1) ed
      (fun _ res => iprop(⌜res ≠ some .timeout⌝)) $$ [Hbuf Hw]
    as %n %err ⟨%k, %res, %Hres, Hbuf, %Hn, #Herr⟩
  · iframe Hca Hbuf Hed
    iapply write_au cn γw γr γx _ $$ Hinv Hw
  cases res with
  | none =>
    iunfold net.resErr at Herr
    icases Herr with %Herr
    subst Herr
    wp_auto
    iapply HΦ
    itrivial
  | some e =>
    iunfold net.resErr at Herr
    icases Herr with ⟨%e', Hop, #Hk⟩
    iunfold net.opErr at Hop
    icases Hop with ⟨%pe, %Hpe, #Hpe⟩
    subst Hpe
    cases e with
    | timeout => exact absurd rfl Hres
    | closed =>
      iunfold net.kindErr at Hk
      icases Hk with %Hk
      subst Hk
      ihave #H2 := Hpe
      iStructNamed H2
      wp_auto
      wp_apply wp_Timeout pe _ $$ [Hpe] as %b %Hb
      · iexact Hpe
      have hb : b = false := Hb.1 rfl
      subst hb
      wp_auto
      iapply HΦ
      itrivial
    | sys =>
      iunfold net.kindErr at Hk
      iunfold net.sysErr at Hk
      icases Hk with ⟨%p, %name, %nn, ⟨%Hk, -, -⟩, -⟩
      subst Hk
      ihave #H2 := Hpe
      iStructNamed H2
      wp_auto
      iapply HΦ
      itrivial

end proof

end github_com.mit_pdos.etcd_grove.examples.axiomcx.tcp_writedeadline
end Perennial

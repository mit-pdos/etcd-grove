/-
The protocol of `examples/net/shutdown`, over the TCP extension's resources (`GooseLang/Ext/Tcp`)
and the per-address protocol (`wire/Addr.lean`):

* **The address** `Addr`'s invariant (`wire.addrInv`): every dialer deposits its connection's
  acceptor end (`connProto cn`, fresh), which the accept loop takes and closes.
* **The listener** (`lisInv hL l γo`, an invariant `Run` allocates after its `Listen`): its state
  `tcpLis hL l Addr o`, shared by the accept loop and the main thread, with a ghost variable `γo`
  mirroring `o`, whose other half is the main thread's. The main thread's `Close` sets both to
  `false` (`lis_close_au`); its last `Accept` then sees `o = false`, so the success branch of
  `Listener.Accept`'s update is vacuous and the `Accept` fails (`closed_accept_au`).
* **The dialer's end** (`endInv cn γc`, an invariant `Run` allocates after its `Dial`): the end's
  state and written bytes, shared by the reader goroutine (`reader_read_au`) and the main thread,
  with a ghost variable `γc` (the main thread's other half) that, once `true`, says the end is
  closed. The main thread's first `Close` sets it (`first_close_au`: a close that cannot fail
  leaves the end closed, whatever it returns), and nothing reopens an end (a failure's `onFail`
  keeps `closed`), so the `Write`, the `Read` and the second `Close` after it fail
  (`closed_write_au`, `closed_read_au`, `closed_close_au`).
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.shutdown.Base
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Addr
public import Perennial.Ghost.GhostVar

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap ndot_mask)

namespace github_com.mit_pdos.etcd_grove.examples.net.shutdown

/-- The node's address, as a Go string. -/
abbrev addr : GoString := go!"127.0.0.1:7106"

def addrN : Namespace := nroot.@"shutdown_addr"
def lisN : Namespace := nroot.@"shutdown_lis"
def endN : Namespace := nroot.@"shutdown_end"

/-- A closed end blocks writes. -/
theorem blocked_of_closed (st : TcpEnd) (h : st.closed = true) : st.blocked = true := by
  simp [TcpEnd.blocked, h]

/-- A close that cannot fail leaves the end closed. -/
theorem closeRes_closed {st : TcpEnd} {f ok : Bool} {st' : TcpEnd} {f' : Bool}
    (h : CloseRes false (fun st => { st with closed := true }) st f ok st' f') :
    st'.closed = true := by
  rcases h with ⟨hc, -, rfl, -⟩ | ⟨-, rfl, -⟩
  · rcases hc with hc | hc
    · cases hc
    · exact hc
  · rfl

/-- A close of a closed end fails and changes nothing. -/
theorem closeRes_of_closed {st : TcpEnd} {f ok : Bool} {st' : TcpEnd} {f' : Bool}
    (hc : st.closed = true)
    (h : CloseRes false (fun st => { st with closed := true }) st f ok st' f') :
    ok = false ∧ st' = st := by
  rcases h with ⟨-, hok, hst, -⟩ | ⟨hc', -, -⟩
  · exact ⟨hok, hst⟩
  · rw [hc] at hc'; cases hc'

/-- A write on a closed end writes nothing and fails. -/
theorem writeRes_of_closed {st : TcpEnd} {bs : GoString} {k : Nat} {ok : Bool} {st' : TcpEnd}
    (hc : st.closed = true) (h : WriteRes st bs k ok st') : ok = false ∧ st' = st := by
  rcases h with ⟨-, -, hok, hst⟩ | ⟨hb, -⟩
  · exact ⟨hok, hst⟩
  · rw [blocked_of_closed st hc] at hb; cases hb

section defs
variable {GF : BundledGFunctors}

/-- A half of the ghost variable `γ` (the listener's openness, the end's closedness). -/
def half {A : Type} [Pos.Countable A] (hT : TcpGS GF) (γ : GName) (a : A) : IProp GF :=
  @ghostVar GF hT.allG A _ γ (1 : Qp).half a

instance half_timeless {A : Type} [Pos.Countable A] (hT : TcpGS GF) (γ : GName) (a : A) :
    Timeless (half hT γ a) := by
  unfold half; letI := hT.allG; infer_instance

/-- The listener `l` at `Addr`, open if `γo`'s value is `true`. -/
def lisInv (hT : TcpGS GF) (hL : TcpLocalGS GF) (l : w64) (γo : GName) : IProp GF :=
  iprop(∃ o : Bool, tcpLis hL l addr o ∗ half hT γo o)

instance lisInv_timeless (hT : TcpGS GF) (hL : TcpLocalGS GF) (l : w64) (γo : GName) :
    Timeless (lisInv hT hL l γo) := by
  unfold lisInv; infer_instance

/-- The dialer's end of `cn`: closed once `γc`'s value is `true`. -/
def endInv (hT : TcpGS GF) (cn : Nat) (γc : GName) : IProp GF :=
  iprop(∃ (st : TcpEnd) (r : Nat) (out : GoString) (f b : Bool),
    tcpEnd hT cn false st r ∗ tcpOut hT cn false out f ∗ half hT γc b ∗
    ⌜b = true → st.closed = true⌝)

instance endInv_timeless (hT : TcpGS GF) (cn : Nat) (γc : GName) :
    Timeless (endInv hT cn γc) := by
  unfold endInv; infer_instance

end defs

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- What the acceptor gets when it accepts `cn`: its fresh end. -/
def connProto (cn : Nat) : IProp GF := tcpFreshEnd (G (Gg := Gg)) cn true

instance connProto_timeless (cn : Nat) : Timeless (connProto (Gg := Gg) cn) := by
  unfold connProto tcpFreshEnd; infer_instance

theorem half_agree {A : Type} [Pos.Countable A] (γ : GName) (a b : A) :
    half (G (Gg := Gg)) γ a -∗ half G γ b -∗ ⌜a = b⌝ := by
  unfold half
  letI := (G (Gg := Gg)).allG
  iintro H1 H2
  iapply ghostVar_agree $$ H1 H2

theorem half_update {A : Type} [Pos.Countable A] (γ : GName) (a b c : A) :
    half (G (Gg := Gg)) γ a -∗ half G γ b ==∗ half G γ c ∗ half G γ c := by
  unfold half
  letI := (G (Gg := Gg)).allG
  iintro H1 H2
  iapply ghostVar_update_halves $$ H1 H2

theorem half_alloc {A : Type} [Pos.Countable A] (a : A) :
    ⊢ |==> ∃ γ, half (G (Gg := Gg)) γ a ∗ half G γ a := by
  unfold half
  letI := (G (Gg := Gg)).allG
  imod ghostVar_alloc (GF := GF) a with ⟨%γ, H⟩
  imodintro
  iexists γ
  iapply (ghostVar_split_half (GF := GF) γ 1 a).1 $$ H

/-- The listener's invariant, allocated from the open listener. -/
theorem lisInv_alloc (hL : TcpLocalGS GF) (l : w64) :
    tcpLis hL l addr true ={⊤}=∗ ∃ γo, inv lisN (lisInv (G (Gg := Gg)) hL l γo) ∗
      half G γo true := by
  iintro Hl
  imod half_alloc (Gg := Gg) true with ⟨%γo, H1, H2⟩
  imod inv_alloc lisN ⊤ (lisInv (G (Gg := Gg)) hL l γo) $$ [Hl H1] with #Hinv
  · inext
    unfold lisInv
    iexists true
    iframe Hl H1
  imodintro
  iexists γo
  iframe Hinv H2

/-- The accept loop's `Accept`: a failure changes nothing, a connection (of an open listener)
hands the acceptor its fresh end. -/
theorem loop_accept_au (hL : TcpLocalGS GF) (l : w64) (γo : GName) :
    ⊢ inv addrN (addrInv addr (connProto (Gg := Gg))) -∗ inv lisN (lisInv G hL l γo) -∗
      |={⊤,∅}=> ∃ o S, tcpLis hL l addr o ∗ tcpPend G addr S ∗
        ((tcpLis hL l addr o -∗ tcpPend G addr S ={∅,⊤}=∗ True) ∧
          (⌜o = true⌝ -∗ ∀ cn, ⌜cn ∈ S⌝ -∗ tcpLis hL l addr o -∗ tcpPend G addr (S \ {[cn]}) -∗
            tcpConnAt G cn addr ={∅,⊤}=∗ connProto cn)) := by
  iintro #Ha #Hl
  iinv Hl with Hli Hclose
  unfold lisInv
  icases Hli with ⟨%o, >Hlis, >Hh⟩
  iinv Ha with Hai Hclose'
  · exact ndot_mask nroot "shutdown_addr" "shutdown_lis" (by decide)
  unfold addrInv
  icases Hai with ⟨%S, >Hpend, >Hdeps⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists o, S
  iframe Hlis Hpend
  isplit
  · iintro Hlis Hpend
    imod Hmask
    imod Hclose' $$ [Hpend Hdeps] with -
    · inext
      iexists S
      iframe Hpend Hdeps
    imod Hclose $$ [Hlis Hh] with -
    · inext
      iexists o
      iframe Hlis Hh
    imodintro
    itrivial
  · iintro %ho %cn %HcS Hlis Hpend #Hat
    imod Hmask
    have hl : PartialMap.get? (setMap S) cn = some () := by
      rw [gmap_get?_eq]; exact (GMap.elem_of_gset _ _).1 HcS
    icases (BigSepM.bigSepM_delete hl).1 $$ Hdeps with ⟨Hp, Hdeps⟩
    rw [wire.setMap_delete]
    imod Hclose' $$ [Hpend Hdeps] with -
    · inext
      iexists S \ {[cn]}
      iframe Hpend Hdeps
    imod Hclose $$ [Hlis Hh] with -
    · inext
      iexists o
      iframe Hlis Hh
    imodintro
    iexact Hp

/-- The main thread's `Close` of the listener: it is closed after, and so is `γo`. -/
theorem lis_close_au (hL : TcpLocalGS GF) (l : w64) (γo : GName) :
    ⊢ inv lisN (lisInv (G (Gg := Gg)) hL l γo) -∗ half G γo true -∗
      |={⊤,∅}=> ∃ o, tcpLis hL l addr o ∗ (tcpLis hL l addr false ={∅,⊤}=∗ half G γo false) := by
  iintro #Hl Hh
  iinv Hl with Hli Hclose
  unfold lisInv
  icases Hli with ⟨%o, >Hlis, >Hh'⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists o
  iframe Hlis
  iintro Hlis
  imod Hmask
  imod half_update (Gg := Gg) γo true o false $$ Hh Hh' with ⟨Hh, Hh'⟩
  imod Hclose $$ [Hlis Hh'] with -
  · inext
    iexists false
    iframe Hlis Hh'
  imodintro
  iexact Hh

/-- The main thread's `Accept` after its `Close`: the listener is closed, so only the failure
branch remains. -/
theorem closed_accept_au (hL : TcpLocalGS GF) (l : w64) (γo : GName) :
    ⊢ inv addrN (addrInv addr (connProto (Gg := Gg))) -∗ inv lisN (lisInv G hL l γo) -∗
      half G γo false -∗
      |={⊤,∅}=> ∃ o S, tcpLis hL l addr o ∗ tcpPend G addr S ∗
        ((tcpLis hL l addr o -∗ tcpPend G addr S ={∅,⊤}=∗ True) ∧
          (⌜o = true⌝ -∗ ∀ cn, ⌜cn ∈ S⌝ -∗ tcpLis hL l addr o -∗ tcpPend G addr (S \ {[cn]}) -∗
            tcpConnAt G cn addr ={∅,⊤}=∗ False)) := by
  iintro #Ha #Hl Hh
  iinv Hl with Hli Hclose
  unfold lisInv
  icases Hli with ⟨%o, >Hlis, >Hh'⟩
  icases half_agree (Gg := Gg) γo false o $$ Hh Hh' with %Ho
  subst Ho
  iinv Ha with Hai Hclose'
  · exact ndot_mask nroot "shutdown_addr" "shutdown_lis" (by decide)
  unfold addrInv
  icases Hai with ⟨%S, >Hpend, >Hdeps⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists false, S
  iframe Hlis Hpend
  isplit
  · iintro Hlis Hpend
    imod Hmask
    imod Hclose' $$ [Hpend Hdeps] with -
    · inext
      iexists S
      iframe Hpend Hdeps
    imod Hclose $$ [Hlis Hh'] with -
    · inext
      iexists false
      iframe Hlis Hh'
    imodintro
    itrivial
  · iintro %ho
    cases ho

/-- The dialer's end's invariant, allocated from its fresh end: not closed yet. -/
theorem endInv_alloc (cn : Nat) :
    tcpFreshEnd (G (Gg := Gg)) cn false ={⊤}=∗ ∃ γc, inv endN (endInv G cn γc) ∗
      half G γc false := by
  iintro Hd
  unfold tcpFreshEnd
  icases Hd with ⟨Hend, Hout⟩
  imod half_alloc (Gg := Gg) false with ⟨%γc, H1, H2⟩
  imod inv_alloc endN ⊤ (endInv (G (Gg := Gg)) cn γc) $$ [Hend Hout H1] with #Hinv
  · inext
    unfold endInv
    iexists TcpEnd.fresh, 0, [], false, false
    iframe Hend Hout H1
    ipureintro; intro h; cases h
  imodintro
  iexists γc
  iframe Hinv H2

/-- The reader goroutine's `Read`: whatever it gives, the end stays closed if it was. -/
theorem reader_read_au (cn : Nat) (γc : GName) (n : w64) :
    ⊢ inv endN (endInv (G (Gg := Gg)) cn γc) -∗
      |={⊤,∅}=> ∃ st r, tcpEnd G cn false st r ∗
        ∀ res, ReadPost G cn false n st r res ={∅,⊤}=∗ True := by
  iintro #Hinv
  iinv Hinv with Hi Hclose
  unfold endInv
  icases Hi with ⟨%st, %r, %out, %f, %b, >Hend, >Hout, >Hh, >%Hb⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, r
  iframe Hend
  iintro %res Hpost
  imod Hmask
  unfold ReadPost
  icases Hpost with (⟨-, Hend⟩ | ⟨-, Hend⟩ | ⟨%bs, %sent, -, -, Hend⟩ | ⟨%sent, -, -, Hend⟩)
  · imod Hclose $$ [Hend Hout Hh] with -
    · inext
      iexists st.onFail, r, out, f, b
      iframe Hend Hout Hh
      ipureintro; intro h; rw [onFail_closed]; exact Hb h
    imodintro
    itrivial
  · imod Hclose $$ [Hend Hout Hh] with -
    · inext
      iexists st, r, out, f, b
      iframe Hend Hout Hh
      ipureintro; exact Hb
    imodintro
    itrivial
  · imod Hclose $$ [Hend Hout Hh] with -
    · inext
      iexists st, r + bs.length, out, f, b
      iframe Hend Hout Hh
      ipureintro; exact Hb
    imodintro
    itrivial
  · imod Hclose $$ [Hend Hout Hh] with -
    · inext
      iexists st, r, out, f, b
      iframe Hend Hout Hh
      ipureintro; exact Hb
    imodintro
    itrivial

/-- The main thread's first `Close`: the end is closed after it, whatever it returns. -/
theorem first_close_au (cn : Nat) (γc : GName) :
    ⊢ inv endN (endInv (G (Gg := Gg)) cn γc) -∗ half G γc false -∗
      |={⊤,∅}=> ∃ st r out f, tcpEnd G cn false st r ∗ tcpOut G cn false out f ∗
        ∀ ok st' f', ⌜CloseRes false (fun st => { st with closed := true }) st f ok st' f'⌝ -∗
          tcpEnd G cn false st' r -∗ tcpOut G cn false out f' ={∅,⊤}=∗ half G γc true := by
  iintro #Hinv Hh
  iinv Hinv with Hi Hclose
  unfold endInv
  icases Hi with ⟨%st, %r, %out, %f, %b, >Hend, >Hout, >Hh', >%Hb⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, r, out, f
  iframe Hend Hout
  iintro %ok %st' %f' %Hcr Hend Hout
  imod Hmask
  imod half_update (Gg := Gg) γc false b true $$ Hh Hh' with ⟨Hh, Hh'⟩
  imod Hclose $$ [Hend Hout Hh'] with -
  · inext
    iexists st', r, out, f', true
    iframe Hend Hout Hh'
    ipureintro; intro _; exact closeRes_closed Hcr
  imodintro
  iexact Hh

/-- A `Write` after the close: it fails. -/
theorem closed_write_au (cn : Nat) (γc : GName) (bs : GoString) :
    ⊢ inv endN (endInv (G (Gg := Gg)) cn γc) -∗ half G γc true -∗
      |={⊤,∅}=> ∃ st r out f, tcpEnd G cn false st r ∗ tcpOut G cn false out f ∗
        ∀ k ok st', ⌜WriteRes st bs k ok st'⌝ -∗ tcpEnd G cn false st' r -∗
          tcpOut G cn false (out ++ bs.take k) f ={∅,⊤}=∗ half G γc true ∗ ⌜ok = false⌝ := by
  iintro #Hinv Hh
  iinv Hinv with Hi Hclose
  unfold endInv
  icases Hi with ⟨%st, %r, %out, %f, %b, >Hend, >Hout, >Hh', >%Hb⟩
  icases half_agree (Gg := Gg) γc true b $$ Hh Hh' with %Heq
  subst Heq
  have hc := Hb rfl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, r, out, f
  iframe Hend Hout
  iintro %k %ok %st' %Hwr Hend Hout
  imod Hmask
  obtain ⟨hok, hst⟩ := writeRes_of_closed hc Hwr
  imod Hclose $$ [Hend Hout Hh'] with -
  · inext
    iexists st', r, out ++ bs.take k, f, true
    iframe Hend Hout Hh'
    ipureintro; intro _; rw [hst]; exact hc
  imodintro
  iframe Hh
  ipureintro; exact hok

/-- A `Read` after the close: it fails. -/
theorem closed_read_au (cn : Nat) (γc : GName) (n : w64) :
    ⊢ inv endN (endInv (G (Gg := Gg)) cn γc) -∗ half G γc true -∗
      |={⊤,∅}=> ∃ st r, tcpEnd G cn false st r ∗
        ∀ res, ReadPost G cn false n st r res ={∅,⊤}=∗
          half G γc true ∗ ⌜res = readRes [] 2⌝ := by
  iintro #Hinv Hh
  iinv Hinv with Hi Hclose
  unfold endInv
  icases Hi with ⟨%st, %r, %out, %f, %b, >Hend, >Hout, >Hh', >%Hb⟩
  icases half_agree (Gg := Gg) γc true b $$ Hh Hh' with %Heq
  subst Heq
  have hc := Hb rfl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, r
  iframe Hend
  iintro %res Hpost
  imod Hmask
  unfold ReadPost
  icases Hpost with (⟨%Hr, Hend⟩ | ⟨%Hr, -⟩ | ⟨%bs, %sent, %Hr, -, -⟩ | ⟨%sent, %Hr, -, -⟩)
  · imod Hclose $$ [Hend Hout Hh'] with -
    · inext
      iexists st.onFail, r, out, f, true
      iframe Hend Hout Hh'
      ipureintro; intro _; rw [onFail_closed]; exact hc
    imodintro
    iframe Hh
    ipureintro; exact Hr
  · rw [hc] at Hr; cases Hr.1
  · rw [hc] at Hr; cases Hr.1
  · rw [hc] at Hr; cases Hr.1

/-- A second `Close`: it fails. -/
theorem closed_close_au (cn : Nat) (γc : GName) :
    ⊢ inv endN (endInv (G (Gg := Gg)) cn γc) -∗ half G γc true -∗
      |={⊤,∅}=> ∃ st r out f, tcpEnd G cn false st r ∗ tcpOut G cn false out f ∗
        ∀ ok st' f', ⌜CloseRes false (fun st => { st with closed := true }) st f ok st' f'⌝ -∗
          tcpEnd G cn false st' r -∗ tcpOut G cn false out f' ={∅,⊤}=∗
          half G γc true ∗ ⌜ok = false⌝ := by
  iintro #Hinv Hh
  iinv Hinv with Hi Hclose
  unfold endInv
  icases Hi with ⟨%st, %r, %out, %f, %b, >Hend, >Hout, >Hh', >%Hb⟩
  icases half_agree (Gg := Gg) γc true b $$ Hh Hh' with %Heq
  subst Heq
  have hc := Hb rfl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, r, out, f
  iframe Hend Hout
  iintro %ok %st' %f' %Hcr Hend Hout
  imod Hmask
  obtain ⟨hok, hst⟩ := closeRes_of_closed hc Hcr
  imod Hclose $$ [Hend Hout Hh'] with -
  · inext
    iexists st', r, out, f', true
    iframe Hend Hout Hh'
    ipureintro; intro _; rw [hst]; exact hc
  imodintro
  iframe Hh
  ipureintro; exact hok

end wps

end github_com.mit_pdos.etcd_grove.examples.net.shutdown
end Perennial

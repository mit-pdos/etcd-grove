/-
The protocol of `examples/net/shutdown`, over the TCP extension's resources (`GooseLang/Ext/Tcp`)
and the per-address protocol (`wire/Addr.lean`):

* **The acceptor's directions** (`downInv γm`, one invariant): for every connection registered in
  the ghost map `γm` (`downReg γm cn`, persistent), its direction from the acceptor
  (`tcpDir cn true`), which the dialer's reader goroutine reads and the accept loop's `Close`
  shuts. The dialer registers its connection in its deposit (`shut_deposit`), so that every
  resource the address's invariant holds is timeless.
* **The address** `Addr`'s invariant (`wire.addrInv`): every dialer deposits its connection's
  acceptor end (`connProto γm cn`: its fresh `tcpEnd`, and the registration), which the accept
  loop takes and closes (`acc_close_au`).
* **The listener** (`lisInv hL l γo`, an invariant `Run` allocates after its `Listen`): its state
  `tcpLis hL l Addr o`, shared by the accept loop and the main thread, with a ghost variable `γo`
  mirroring `o`, whose other half is the main thread's. The main thread's `Close` sets both to
  `false` (`lis_close_au`); its last `Accept` then sees `o = false`, so the success branch of
  `Listener.Accept`'s update is vacuous and the `Accept` fails (`closed_accept_au`).
* **The dialer's end** (`endInv cn γc`, an invariant `Run` allocates after its `Dial`): the end's
  state (`tcpEnd cn false`) and its direction (`tcpDir cn false`), shared by the reader goroutine
  (`reader_read_au`) and the main thread, with a ghost variable `γc` (the main thread's other half)
  that, once `true`, says the end is closed. The main thread's first `Close` sets it
  (`first_close_au`: a close leaves the end closed, whatever it returns), and nothing reopens an
  end (a read does not change the end's state, a write or a close of a closed end neither), so the
  `Write`, the `Read` and the second `Close` after it fail (`closed_write_au`, `closed_read_au`,
  `closed_close_au`): on a closed end, `WriteOutcome`, `ReadOutcome` and `CloseOutcome` give only
  an error.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.shutdown.Base
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Addr
public import Perennial.Ghost.GhostVar
public import Perennial.Ghost.GhostMap

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
def downN : Namespace := nroot.@"shutdown_down"

/-! ## The outcomes on a closed end -/

/-- A close leaves the end closed, whatever it returns. -/
theorem closeOutcome_closed {st : TcpEnd} {d : TcpDir} {ok : Bool} {st' : TcpEnd} {d' : TcpDir}
    (h : CloseOutcome st d ok st' d') : st'.closed = true := by
  unfold CloseOutcome at h
  split at h
  · rw [h.2.1]; assumption
  · rw [h.1]

/-- A close of a closed end fails and changes nothing. -/
theorem closeOutcome_of_closed {st : TcpEnd} {d : TcpDir} {ok : Bool} {st' : TcpEnd}
    {d' : TcpDir} (hc : st.closed = true) (h : CloseOutcome st d ok st' d') :
    ok = false ∧ st' = st := by
  simp only [CloseOutcome, hc, ↓reduceIte] at h
  exact ⟨h.1, h.2.1⟩

/-- A write on a closed end fails. -/
theorem writeOutcome_of_closed {st : TcpEnd} {d : TcpDir} {bs : List w8} {k : Nat} {ok : Bool}
    {d' : TcpDir} (hc : st.closed = true) (h : WriteOutcome st d bs k ok d') : ok = false := by
  simp only [WriteOutcome, hc, Bool.true_or, ↓reduceIte] at h
  exact h.2.1

/-- A read on a closed end fails. -/
theorem readOutcome_of_closed {st : TcpEnd} {d : TcpDir} {n : Nat} {r : ReadRes} {d' : TcpDir}
    (hc : st.closed = true) (h : ReadOutcome st d n r d') : r = .err := by
  simp only [ReadOutcome, hc, ↓reduceIte] at h
  exact h.1

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

/-- The dialer's end of `cn` and its direction: closed once `γc`'s value is `true`. -/
def endInv (hT : TcpGS GF) (cn : Nat) (γc : GName) : IProp GF :=
  iprop(∃ (st : TcpEnd) (d : TcpDir) (b : Bool),
    tcpEnd hT cn false st ∗ tcpDir hT cn false d ∗ half hT γc b ∗
    ⌜b = true → st.closed = true⌝)

instance endInv_timeless (hT : TcpGS GF) (cn : Nat) (γc : GName) :
    Timeless (endInv hT cn γc) := by
  unfold endInv; infer_instance

/-- The acceptor's direction of every connection registered in `γm`. -/
def downInv (hT : TcpGS GF) (γm : GName) : IProp GF :=
  iprop(∃ m : GMap Nat Unit, @ghostMapAuth GF hT.allG Nat Unit _ _ γm 1 m ∗
    [∗map] cn ↦ _u ∈ m, ∃ d, tcpDir hT cn true d)

/-- The connection `cn` is registered in `γm`: `downInv γm` holds its acceptor's direction. -/
def downReg (hT : TcpGS GF) (γm : GName) (cn : Nat) : IProp GF :=
  @ghostMapElem GF hT.allG Nat Unit _ _ γm cn .discard ()

instance downReg_persistent (hT : TcpGS GF) (γm : GName) (cn : Nat) :
    Persistent (downReg hT γm cn) := by
  unfold downReg; letI := hT.allG; infer_instance

instance downReg_timeless (hT : TcpGS GF) (γm : GName) (cn : Nat) :
    Timeless (downReg hT γm cn) := by
  unfold downReg; letI := hT.allG; infer_instance

end defs

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- What the acceptor gets when it accepts `cn`: its fresh end, and that its direction is in
`downInv γm`. -/
def connProto (γm : GName) (cn : Nat) : IProp GF :=
  iprop(tcpEnd (G (Gg := Gg)) cn true TcpEnd.fresh ∗ downReg G γm cn)

instance connProto_timeless (γm : GName) (cn : Nat) : Timeless (connProto (Gg := Gg) γm cn) := by
  unfold connProto; infer_instance

/-- The invariants of the protocol. -/
def shutInvs (γm : GName) : IProp GF :=
  iprop(inv addrN (addrInv addr (connProto (Gg := Gg) γm)) ∗ inv downN (downInv G γm))

instance shutInvs_persistent (γm : GName) : Persistent (shutInvs (Gg := Gg) γm) := by
  unfold shutInvs; infer_instance

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

/-- A dialer's deposit for its new connection `cn`: the acceptor's direction registered in
`downInv γm`, and the acceptor's end with the registration for the accept loop. -/
theorem shut_deposit (γm : GName) (cn : Nat) :
    ⊢ inv downN (downInv (G (Gg := Gg)) γm) -∗ tcpFresh G cn true ={⊤ \ ↑addrN}=∗
      connProto γm cn ∗ downReg G γm cn := by
  iintro #Hinv Ha
  iinv Hinv with Hi Hclose
  · exact ndot_mask nroot "shutdown_down" "shutdown_addr" (by decide)
  unfold downInv
  icases Hi with ⟨%m, >Hm, >Hdirs⟩
  unfold tcpFresh
  icases Ha with ⟨Hae, Had⟩
  letI := (G (Gg := Gg)).allG
  cases hm : m.lookup cn with
  | some u =>
    -- `cn` is new: its acceptor's direction is owned once
    icases BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some u by
      rw [gmap_get?_eq]; exact hm) $$ Hdirs with ⟨⟨%d, Hd⟩, -⟩
    icases tcpDir_excl _ cn true d TcpDir.fresh $$ Hd Had with ⟨⟩
  | none =>
    imod ghost_map_insert_persist cn () hm $$ Hm with ⟨Hm, #Hreg⟩
    imod Hclose $$ [Hm Hdirs Had] with -
    · inext
      iexists m.insert cn ()
      iframe Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m cn = none by
        rw [gmap_get?_eq]; exact hm)).2
      iframe Hdirs
      iexists TcpDir.fresh
      iexact Had
    imodintro
    unfold connProto downReg
    iframe Hae Hreg

/-- The acceptor's direction of a registered connection, from `downInv`: it and the update that
puts it back. -/
theorem down_acc (γm : GName) (cn : Nat) (E : CoPset) (hE : ↑downN ⊆ E) :
    ⊢ inv downN (downInv (G (Gg := Gg)) γm) -∗ downReg G γm cn -∗
      |={E, E \ ↑downN}=> (∃ d, tcpDir G cn true d) ∗
        ((∃ d, tcpDir G cn true d) ={E \ ↑downN, E}=∗ True) := by
  iintro #Hinv #Hreg
  iinv Hinv with Hi Hclose
  unfold downInv
  icases Hi with ⟨%m, >Hm, >Hdirs⟩
  letI := (G (Gg := Gg)).allG
  unfold downReg
  icases ghost_map_lookup $$ Hm Hreg with %Hl
  icases BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some () by
    rw [gmap_get?_eq]; exact Hl) $$ Hdirs with ⟨Hd, Hback⟩
  imodintro
  iframe Hd
  iintro Hd
  imod Hclose $$ [Hm Hback Hd] with -
  · inext
    iexists m
    iframe Hm
    iapply Hback $$ Hd
  imodintro
  itrivial

/-- The accept loop's `Close` of the end it accepted. -/
theorem acc_close_au (γm : GName) (cn : Nat) (st : TcpEnd) :
    ⊢ inv downN (downInv (G (Gg := Gg)) γm) -∗ downReg G γm cn -∗ tcpEnd G cn true st -∗
      |={⊤,∅}=> ∃ st0 d, tcpEnd G cn true st0 ∗ tcpDir G cn true d ∗
        ∀ ok st' d', ⌜CloseOutcome st0 d ok st' d'⌝ -∗ tcpEnd G cn true st' -∗
          tcpDir G cn true d' ={∅,⊤}=∗ True := by
  iintro #Hinv #Hreg Hend
  imod down_acc γm cn ⊤ (by simp) $$ Hinv Hreg with ⟨⟨%d, Hd⟩, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %ok %st' %d' %Hc Hend Hd
  imod Hmask
  imod Hclose $$ [Hd] with -
  · iexists d'
    iexact Hd
  imodintro
  itrivial

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
hands the acceptor its deposit. -/
theorem loop_accept_au (γm : GName) (hL : TcpLocalGS GF) (l : w64) (γo : GName) :
    ⊢ inv addrN (addrInv addr (connProto (Gg := Gg) γm)) -∗ inv lisN (lisInv G hL l γo) -∗
      |={⊤,∅}=> ∃ o S, tcpLis hL l addr o ∗ tcpPend G addr S ∗
        ((tcpLis hL l addr o -∗ tcpPend G addr S ={∅,⊤}=∗ True) ∧
          (⌜o = true⌝ -∗ ∀ cn, ⌜cn ∈ S⌝ -∗ tcpLis hL l addr o -∗ tcpPend G addr (S \ {[cn]}) -∗
            tcpConnAt G cn addr ={∅,⊤}=∗ connProto γm cn)) := by
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
theorem closed_accept_au (γm : GName) (hL : TcpLocalGS GF) (l : w64) (γo : GName) :
    ⊢ inv addrN (addrInv addr (connProto (Gg := Gg) γm)) -∗ inv lisN (lisInv G hL l γo) -∗
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

/-- The dialer's end's invariant, allocated from its fresh end and direction: not closed yet. -/
theorem endInv_alloc (cn : Nat) :
    tcpFresh (G (Gg := Gg)) cn false ={⊤}=∗ ∃ γc, inv endN (endInv G cn γc) ∗
      half G γc false := by
  iintro Hd
  unfold tcpFresh
  icases Hd with ⟨Hend, Hdir⟩
  imod half_alloc (Gg := Gg) false with ⟨%γc, H1, H2⟩
  imod inv_alloc endN ⊤ (endInv (G (Gg := Gg)) cn γc) $$ [Hend Hdir H1] with #Hinv
  · inext
    unfold endInv
    iexists TcpEnd.fresh, TcpDir.fresh, false
    iframe Hend Hdir H1
    ipureintro; intro h; cases h
  imodintro
  iexists γc
  iframe Hinv H2

/-- The update of a `Read` at the dialer's end, from the acceptor's direction (`downInv`) and the
end's invariant, whose result `Q r` the caller makes from the end's ghost flag `b` and whether
the end is closed. -/
theorem end_read_au (γm : GName) (cn : Nat) (γc : GName) (n : Nat) (P : IProp GF)
    (Q : ReadRes → IProp GF)
    (HQ : ∀ (st : TcpEnd) (b : Bool) (r : ReadRes), (b = true → st.closed = true) →
      (∃ d d', ReadOutcome st d n r d') → (P ∗ half G γc b ⊢ Q r ∗ half G γc b)) :
    ⊢ inv downN (downInv (G (Gg := Gg)) γm) -∗ downReg G γm cn -∗ inv endN (endInv G cn γc) -∗
      P -∗
      |={⊤,∅}=> ∃ st d, tcpEnd G cn false st ∗ tcpDir G cn true d ∗
        ∀ r d', ⌜ReadOutcome st d n r d' ∧ r ≠ .wait⌝ -∗ tcpEnd G cn false st -∗
          tcpDir G cn true d' ={∅,⊤}=∗ Q r := by
  iintro #Hdown #Hreg #Hinv HP
  iinv Hinv with Hi Hclose
  unfold endInv
  icases Hi with ⟨%st, %dd, %b, >Hend, >Hdd, >Hh, >%Hb⟩
  imod down_acc γm cn (⊤ \ ↑endN) (ndot_mask nroot "shutdown_down" "shutdown_end" (by decide))
    $$ Hdown Hreg with ⟨⟨%d, Hd⟩, Hclose'⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %r %d' %Hrd Hend Hd
  imod Hmask
  imod Hclose' $$ [Hd] with -
  · iexists d'
    iexact Hd
  icases (HQ st b r Hb ⟨d, d', Hrd.1⟩) $$ [HP Hh] with ⟨HQr, Hh⟩
  · iframe HP Hh
  imod Hclose $$ [Hend Hdd Hh] with -
  · inext
    iexists st, dd, b
    iframe Hend Hdd Hh
    ipureintro; exact Hb
  imodintro
  iexact HQr

/-- The reader goroutine's `Read`. -/
theorem reader_read_au (γm : GName) (cn : Nat) (γc : GName) (n : Nat) :
    ⊢ inv downN (downInv (G (Gg := Gg)) γm) -∗ downReg G γm cn -∗ inv endN (endInv G cn γc) -∗
      |={⊤,∅}=> ∃ st d, tcpEnd G cn false st ∗ tcpDir G cn true d ∗
        ∀ r d', ⌜ReadOutcome st d n r d' ∧ r ≠ .wait⌝ -∗ tcpEnd G cn false st -∗
          tcpDir G cn true d' ={∅,⊤}=∗ True := by
  iintro #Hdown #Hreg #Hinv
  have HQ : ∀ (st : TcpEnd) (b : Bool) (r : ReadRes), (b = true → st.closed = true) →
      (∃ d d', ReadOutcome st d n r d') →
      (iprop(True) ∗ half (G (Gg := Gg)) γc b ⊢ iprop(True) ∗ half G γc b) := by
    intro st b r _ _
    iintro ⟨-, Hh⟩
    iframe Hh
  iapply end_read_au γm cn γc n iprop(True) (fun _ => iprop(True)) HQ $$ Hdown Hreg Hinv
  itrivial

/-- A `Read` after the close: it fails. -/
theorem closed_read_au (γm : GName) (cn : Nat) (γc : GName) (n : Nat) :
    ⊢ inv downN (downInv (G (Gg := Gg)) γm) -∗ downReg G γm cn -∗ inv endN (endInv G cn γc) -∗
      half G γc true -∗
      |={⊤,∅}=> ∃ st d, tcpEnd G cn false st ∗ tcpDir G cn true d ∗
        ∀ r d', ⌜ReadOutcome st d n r d' ∧ r ≠ .wait⌝ -∗ tcpEnd G cn false st -∗
          tcpDir G cn true d' ={∅,⊤}=∗ half G γc true ∗ ⌜r = .err⌝ := by
  iintro #Hdown #Hreg #Hinv Hh
  have HQ : ∀ (st : TcpEnd) (b : Bool) (r : ReadRes), (b = true → st.closed = true) →
      (∃ d d', ReadOutcome st d n r d') →
      (half (G (Gg := Gg)) γc true ∗ half G γc b ⊢ iprop(half G γc true ∗ ⌜r = .err⌝) ∗
        half G γc b) := by
    intro st b r Hb Hr
    iintro ⟨Hh, Hh'⟩
    icases half_agree (Gg := Gg) γc true b $$ Hh Hh' with %Heq
    subst Heq
    obtain ⟨d, d', Hr⟩ := Hr
    iframe Hh Hh'
    ipureintro; exact readOutcome_of_closed (Hb rfl) Hr
  iapply end_read_au γm cn γc n (half G γc true) (fun r => iprop(half G γc true ∗ ⌜r = .err⌝))
    HQ $$ Hdown Hreg Hinv Hh

/-- The main thread's first `Close`: the end is closed after it, whatever it returns. -/
theorem first_close_au (cn : Nat) (γc : GName) :
    ⊢ inv endN (endInv (G (Gg := Gg)) cn γc) -∗ half G γc false -∗
      |={⊤,∅}=> ∃ st d, tcpEnd G cn false st ∗ tcpDir G cn false d ∗
        ∀ ok st' d', ⌜CloseOutcome st d ok st' d'⌝ -∗ tcpEnd G cn false st' -∗
          tcpDir G cn false d' ={∅,⊤}=∗ half G γc true := by
  iintro #Hinv Hh
  iinv Hinv with Hi Hclose
  unfold endInv
  icases Hi with ⟨%st, %d, %b, >Hend, >Hd, >Hh', >%Hb⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %ok %st' %d' %Hc Hend Hd
  imod Hmask
  imod half_update (Gg := Gg) γc false b true $$ Hh Hh' with ⟨Hh, Hh'⟩
  imod Hclose $$ [Hend Hd Hh'] with -
  · inext
    iexists st', d', true
    iframe Hend Hd Hh'
    ipureintro; intro _; exact closeOutcome_closed Hc
  imodintro
  iexact Hh

/-- A `Write` after the close: it fails. -/
theorem closed_write_au (cn : Nat) (γc : GName) (bs : List w8) :
    ⊢ inv endN (endInv (G (Gg := Gg)) cn γc) -∗ half G γc true -∗
      |={⊤,∅}=> ∃ st d, tcpEnd G cn false st ∗ tcpDir G cn false d ∗
        ∀ k ok d', ⌜WriteOutcome st d bs k ok d'⌝ -∗ tcpEnd G cn false st -∗
          tcpDir G cn false d' ={∅,⊤}=∗ half G γc true ∗ ⌜ok = false⌝ := by
  iintro #Hinv Hh
  iinv Hinv with Hi Hclose
  unfold endInv
  icases Hi with ⟨%st, %d, %b, >Hend, >Hd, >Hh', >%Hb⟩
  icases half_agree (Gg := Gg) γc true b $$ Hh Hh' with %Heq
  subst Heq
  have hc := Hb rfl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %k %ok %d' %Hwr Hend Hd
  imod Hmask
  imod Hclose $$ [Hend Hd Hh'] with -
  · inext
    iexists st, d', true
    iframe Hend Hd Hh'
    ipureintro; intro _; exact hc
  imodintro
  iframe Hh
  ipureintro; exact writeOutcome_of_closed hc Hwr

/-- A second `Close`: it fails. -/
theorem closed_close_au (cn : Nat) (γc : GName) :
    ⊢ inv endN (endInv (G (Gg := Gg)) cn γc) -∗ half G γc true -∗
      |={⊤,∅}=> ∃ st d, tcpEnd G cn false st ∗ tcpDir G cn false d ∗
        ∀ ok st' d', ⌜CloseOutcome st d ok st' d'⌝ -∗ tcpEnd G cn false st' -∗
          tcpDir G cn false d' ={∅,⊤}=∗ half G γc true ∗ ⌜ok = false⌝ := by
  iintro #Hinv Hh
  iinv Hinv with Hi Hclose
  unfold endInv
  icases Hi with ⟨%st, %d, %b, >Hend, >Hd, >Hh', >%Hb⟩
  icases half_agree (Gg := Gg) γc true b $$ Hh Hh' with %Heq
  subst Heq
  have hc := Hb rfl
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %ok %st' %d' %Hc Hend Hd
  imod Hmask
  obtain ⟨hok, hst⟩ := closeOutcome_of_closed hc Hc
  imod Hclose $$ [Hend Hd Hh'] with -
  · inext
    iexists st', d', true
    iframe Hend Hd Hh'
    ipureintro; intro _; rw [hst]; exact hc
  imodintro
  iframe Hh
  ipureintro; exact hok

end wps

end github_com.mit_pdos.etcd_grove.examples.net.shutdown
end Perennial

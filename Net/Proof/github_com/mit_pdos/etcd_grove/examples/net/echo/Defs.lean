/-
The protocol of `examples/net/echo`, over the net extension's resources (`GooseLang/Ext/Net`), the
per-address protocol (`wire/Addr.lean`) and the per-direction stream protocol (`wire/Stream.lean`):

* **Every connection** `cn` to `srvAddr` has ghost names `γ` (`echoName γm cn γ`, persistent: the
  ghost map `γm`): the two directions' stream protocols (`γ.up`, from the dialer; `γ.down`, from
  the acceptor) and the server's ghost variable (`γ.srv`). Its state (`connInv cn γ`) is both
  directions' `dirInv`s and the echo state (`echoConn γ`): the acceptor's written bytes `Wd` (the
  writer's half `sentAll γ.down Wd`, and half of the server's variable, `echoSrv γ.srv Wd`, whose
  other half the server holds: it knows what it has written so far) are a prefix of a lower bound
  `si` of what the dialer has written (`sentLb γ.up si`). All connections' states are in one
  invariant (`echoState γm`), so
  that every resource the protocol moves is timeless; each direction's `inv echoN (dirInv …)`,
  which `Stream.lean`'s updates take, is derived from it (`echo_dirInv_up`/`_down`, `inv_alter`).
* **The connection's protocol** `connProto γm cn`, which every dialer deposits in `srvAddr`'s
  invariant (`echo_deposit`, through `wire.dial_both_au`) and the server takes when it accepts `cn`
  (`wire.accept_lis_au`): the acceptor end's state, the server's half of `γ.srv` (nothing written),
  the reader's half of the up-direction (with its lower bound `sentLb γ.up []`) and the names. The
  dialer keeps `dialerOwn γm cn`: its end's state, the writer's half of the up-direction, the
  reader's half of the down-direction. A dial that fails but leaves its connection pending
  (abandoned, D16: the dialer's end closed, its direction shut and empty) deposits the same
  `connProto`
  (`echo_deposit_ab`): the up-direction's protocol starts from that shut direction, nothing written
  (`wire.dirInv_body_alloc_of`, `Net.dirOk_abandoned`), so a server that accepts it reads EOF, and
  the dialer keeps nothing.

The client's check (`client_check`): a reply it read (`sentLb γ.down resp`, from `Stream.read_acc`)
is a prefix of the server's bytes `Wd`, which are a prefix of the client's own (its
`sentAll γ.up`). The server's `Write` of the request `bs` it read (`sentLb γ.up bs`) is Go's loop
of steps (D2): its writer predicate `srvP` is its end's state and its half of `γ.srv` at the bytes
`w` written so far, and its accessor (`server_write_acc`) appends each step's bytes to `Wd = w`,
still a prefix of `bs`.
Crashes change nothing here: the invariants are global, and a connection's protocol stays in the
address's invariant until a server (of any incarnation) accepts it.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Stream

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv DirNames dirInv sentAll sentLb rcvdAll)

namespace github_com.mit_pdos.etcd_grove.examples.net.echo

/-- The server's address, as a Go string. -/
abbrev srvAddr : GoString := go!"127.0.0.1:7101"

def addrN : Namespace := nroot.@"echo_addr"
def echoN : Namespace := nroot.@"echo_conns"

/-- The ghost names of a connection: the server's ghost variable (the bytes it has written) and its
two directions' stream protocols. -/
structure EchoNames where
  srv : GName
  up : DirNames
  down : DirNames

def EchoNames.enc (γ : EchoNames) : GName × GName × GName × GName × GName :=
  (γ.srv, γ.up.w, γ.up.r, γ.down.w, γ.down.r)

instance EchoNames.countable : Pos.Countable EchoNames :=
  .ofInjective (fun γ => Pos.Countable.encode γ.enc) (fun a b h => by
    have h' := Pos.encode_inj h
    obtain ⟨t, ⟨uw, ur⟩, ⟨dw, dr⟩⟩ := a
    obtain ⟨t', ⟨uw', ur'⟩, ⟨dw', dr'⟩⟩ := b
    simp only [EchoNames.enc, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h'; rfl)

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- Half of the server's ghost variable of a connection: the bytes it has written on it. -/
def echoSrv (γ : GName) (w : List w8) : IProp GF :=
  @ghostVar GF (G (Gg := Gg)).allG _ _ γ (1 : Qp).half w

instance echoSrv_timeless (γ : GName) (w : List w8) : Timeless (echoSrv (Gg := Gg) γ w) := by
  unfold echoSrv; letI := (G (Gg := Gg)).allG; infer_instance

/-- The echo state of a connection with names `γ`: the acceptor's written bytes, a prefix of what
the dialer has written. -/
def echoConn (γ : EchoNames) : IProp GF :=
  iprop(∃ Wd : List w8, sentAll (Gg := Gg) γ.down Wd ∗ echoSrv γ.srv Wd ∗
    ∃ si, sentLb (Gg := Gg) γ.up si ∗ ⌜Wd <+: si⌝)

instance echoConn_timeless (γ : EchoNames) : Timeless (echoConn (Gg := Gg) γ) := by
  unfold echoConn; infer_instance

/-- The state of the connection `cn`, with names `γ`. -/
def connInv (cn : Nat) (γ : EchoNames) : IProp GF :=
  iprop(dirInv (Gg := Gg) cn false γ.up ∗ dirInv (Gg := Gg) cn true γ.down ∗ echoConn γ)

instance connInv_timeless (cn : Nat) (γ : EchoNames) : Timeless (connInv (Gg := Gg) cn γ) := by
  unfold connInv; infer_instance

/-- Every connection's state, their names in the ghost map `γm`. -/
def echoState (γm : GName) : IProp GF :=
  iprop(∃ m : GMap Nat EchoNames, @ghostMapAuth GF (G (Gg := Gg)).allG _ _ _ _ γm 1 m ∗
    [∗map] cn ↦ γ ∈ m, connInv cn γ)

instance echoState_timeless (γm : GName) : Timeless (echoState (Gg := Gg) γm) := by
  unfold echoState; letI := (G (Gg := Gg)).allG; infer_instance

/-- The connection `cn`'s names are `γ`. -/
def echoName (γm : GName) (cn : Nat) (γ : EchoNames) : IProp GF :=
  @ghostMapElem GF (G (Gg := Gg)).allG _ _ _ _ γm cn .discard γ

instance echoName_persistent (γm : GName) (cn : Nat) (γ : EchoNames) :
    Persistent (echoName (Gg := Gg) γm cn γ) := by
  unfold echoName; letI := (G (Gg := Gg)).allG; infer_instance

instance echoName_timeless (γm : GName) (cn : Nat) (γ : EchoNames) :
    Timeless (echoName (Gg := Gg) γm cn γ) := by
  unfold echoName; letI := (G (Gg := Gg)).allG; infer_instance

/-- What the server gets when it accepts `cn`. -/
def connProto (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, echoName (Gg := Gg) γm cn γ ∗ netEnd G cn true NetEnd.fresh ∗ echoSrv γ.srv [] ∗
    rcvdAll (Gg := Gg) γ.up [] ∗ sentLb (Gg := Gg) γ.up [])

instance connProto_timeless (γm : GName) (cn : Nat) : Timeless (connProto (Gg := Gg) γm cn) := by
  unfold connProto; infer_instance

/-- What the dialer keeps of its new connection `cn`. -/
def dialerOwn (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, echoName (Gg := Gg) γm cn γ ∗ netEnd G cn false NetEnd.fresh ∗
    sentAll (Gg := Gg) γ.up [] ∗ rcvdAll (Gg := Gg) γ.down [] ∗ sentLb (Gg := Gg) γ.down [])

/-- The invariants of the protocol. -/
def echoInvs (γm : GName) : IProp GF :=
  iprop(inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗ inv echoN (echoState (Gg := Gg) γm))

instance echoInvs_persistent (γm : GName) : Persistent (echoInvs (Gg := Gg) γm) := by
  unfold echoInvs; infer_instance

theorem echoInvs_elim (γm : GName) :
    echoInvs (Gg := Gg) γm ⊢ inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗
      inv echoN (echoState (Gg := Gg) γm) := .rfl

/-- The deposit of a new connection `cn`, from the acceptor's fresh end and the dialer's direction
`d` (nothing in it, not cut): both directions' stream protocols, the server's ghost variable, the
names in the map, the connection's state (nothing written yet); the server's part (`connProto`) and
the dialer's halves of the directions. -/
theorem echo_deposit_dir (γm : GName) (cn : Nat) (d : NetDir) (hd : DirOk d [] []) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ netDir G cn false d -∗ netEnd G cn true NetEnd.fresh -∗
      netDir G cn true NetDir.fresh ={⊤ \ ↑addrN}=∗ connProto γm cn ∗
        ∃ γ, echoName γm cn γ ∗ sentAll (Gg := Gg) γ.up [] ∗ rcvdAll (Gg := Gg) γ.down [] ∗
          sentLb (Gg := Gg) γ.down [] := by
  iintro #Hinv Hdd Hae Had
  iinv Hinv with Hi Hclose
  · exact ndot_mask nroot "echo_conns" "echo_addr" (by decide)
  unfold echoState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  letI := (G (Gg := Gg)).allG
  cases hm : m.lookup cn with
  | some γ' =>
    -- `cn` is new: its acceptor's direction is owned once
    icases (BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some γ' by
      rw [gmap_get?_eq]; exact hm)).1 $$ Hconns with ⟨Hc, -⟩
    unfold connInv dirInv
    icases Hc with ⟨-, ⟨%d, %W, %R, Hdir, -⟩, -⟩
    icases netDir_excl _ cn true d NetDir.fresh $$ Hdir Had with ⟨⟩
  | none =>
    imod wire.dirInv_body_alloc_of cn false d hd $$ Hdd with ⟨%γu, HIu, Hwu, Hru⟩
    imod wire.dirInv_body_alloc cn true $$ Had with ⟨%γd, HId, Hwd, Hrd⟩
    imod ghostVar_alloc (GF := GF) ([] : List w8) with ⟨%γt, Hs⟩
    icases (ghostVar_split_half γt 1 ([] : List w8)).mp $$ Hs with ⟨Hs1, Htok⟩
    ihave #Hlbu : (sentLb (Gg := Gg) γu [] : IProp GF) $$ [Hwu]
    · iapply wire.sentLb_get
      iexact Hwu
    ihave #Hlbd : (sentLb (Gg := Gg) γd [] : IProp GF) $$ [Hwd]
    · iapply wire.sentLb_get
      iexact Hwd
    imod ghost_map_insert_persist cn (⟨γt, γu, γd⟩ : EchoNames) hm $$ Hm with ⟨Hm, #Hname⟩
    imod Hclose $$ [Hm Hconns HIu HId Hwd Hs1] with -
    · inext
      iexists m.insert cn ⟨γt, γu, γd⟩
      iframe Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m cn = none by
        rw [gmap_get?_eq]; exact hm)).2
      iframe Hconns
      unfold connInv echoConn
      iframe HIu HId
      iexists []
      unfold echoSrv
      iframe Hwd Hs1
      iexists []
      iframe Hlbu
      ipureintro; exact List.nil_prefix
    imodintro
    unfold connProto echoName echoSrv
    isplitl [Hae Htok Hru]
    · iexists ⟨γt, γu, γd⟩
      iframe Hname Hae Htok Hru Hlbu
    · iexists ⟨γt, γu, γd⟩
      iframe Hname Hwu Hrd Hlbd

/-- A dialer's deposit for its new connection `cn` (`dial_both_au`'s `mk`): `echo_deposit_dir`
from its fresh direction; the dialer keeps `dialerOwn`. -/
theorem echo_deposit (γm : GName) (cn : Nat) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ netConnAt G cn srvAddr -∗ netFresh G cn false -∗
      netFresh G cn true ={⊤ \ ↑addrN}=∗ connProto γm cn ∗ dialerOwn γm cn := by
  iintro #Hinv #- Hd Ha
  unfold netFresh
  icases Hd with ⟨Hde, Hdd⟩
  icases Ha with ⟨Hae, Had⟩
  imod echo_deposit_dir γm cn NetDir.fresh Net.dirOk_fresh $$ Hinv Hdd Hae Had
    with ⟨Hp, %γ, #Hname, Hw, Hr, #Hlb⟩
  imodintro
  iframe Hp
  unfold dialerOwn
  iexists γ
  iframe Hname Hde Hw Hr Hlb

/-- The deposit of a dial that failed leaving its connection `cn` abandoned (D16; `dial_both_au`'s
`mkAb`): `echo_deposit_dir` from the dialer's shut, empty direction (its closed end is dropped).
The server may accept the connection; it reads EOF (the dialer wrote nothing). -/
theorem echo_deposit_ab (γm : GName) (cn : Nat) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ netConnAt G cn srvAddr -∗
      netEnd G cn false { NetEnd.fresh with closed := true } -∗ netDir G cn false ⟨[], .fin⟩ -∗
      netFresh G cn true ={⊤ \ ↑addrN}=∗ connProto γm cn := by
  iintro #Hinv #- - Hdd Ha
  unfold netFresh
  icases Ha with ⟨Hae, Had⟩
  imod echo_deposit_dir γm cn ⟨[], .fin⟩ Net.dirOk_abandoned $$ Hinv Hdd Hae Had with ⟨Hp, -⟩
  imodintro
  iexact Hp

/-- The state of a connection, from the invariant, by its names. -/
theorem echoState_lookup (γm : GName) (cn : Nat) (γ : EchoNames) :
    echoName (Gg := Gg) γm cn γ ⊢ echoState γm -∗ connInv cn γ ∗ (connInv cn γ -∗ echoState γm) := by
  iintro #Hname Hi
  unfold echoState
  icases Hi with ⟨%m, Hm, Hconns⟩
  letI := (G (Gg := Gg)).allG
  unfold echoName
  icases ghost_map_lookup $$ Hm Hname with %Hl
  icases (BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some γ by
    rw [gmap_get?_eq]; exact Hl)).1 $$ Hconns with ⟨Hc, Hback⟩
  iframe Hc
  iintro Hc
  iexists m
  iframe Hm
  iapply Hback $$ Hc

/-- The up-direction's stream invariant of a connection, from the protocol's. -/
theorem echo_dirInv_up (γm : GName) (cn : Nat) (γ : EchoNames) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ echoName γm cn γ -∗
      inv echoN (dirInv (Gg := Gg) cn false γ.up) := by
  iintro #Hinv #Hname
  iapply inv_alter $$ Hinv
  inext
  imodintro
  iintro Hi
  icases echoState_lookup γm cn γ $$ Hname Hi with ⟨Hc, Hback⟩
  unfold connInv
  icases Hc with ⟨Hu, Hd, He⟩
  iframe Hu
  iintro Hu
  iapply Hback
  iframe Hu Hd He

/-- The down-direction's stream invariant of a connection, from the protocol's. -/
theorem echo_dirInv_down (γm : GName) (cn : Nat) (γ : EchoNames) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ echoName γm cn γ -∗
      inv echoN (dirInv (Gg := Gg) cn true γ.down) := by
  iintro #Hinv #Hname
  iapply inv_alter $$ Hinv
  inext
  imodintro
  iintro Hi
  icases echoState_lookup γm cn γ $$ Hname Hi with ⟨Hc, Hback⟩
  unfold connInv
  icases Hc with ⟨Hu, Hd, He⟩
  iframe Hd
  iintro Hd
  iapply Hback
  iframe Hu Hd He

/-- The server's writer predicate (`net.Conn.Write.spec`'s `P`) on `cn`: its end's state `st` and
its half of `γ.srv` at the bytes `w` its `Write` has written so far. -/
def srvP (cn : Nat) (γ : EchoNames) (st : NetEnd) (w : List w8) (_res : Option NetErr) :
    IProp GF :=
  iprop(netEnd G cn true st ∗ echoSrv (Gg := Gg) γ.srv w)

/-- The accessor of the server's `Write` on `cn` (its end's state `st` the thread's) of bytes `bs`
the dialer has written (`sentLb γ.up bs`): a step on the bytes `rs` not yet written (`w ++ rs =
bs`, `w` the echo state's bytes, by the server's half of `γ.srv`) appends what it wrote to the
acceptor's written bytes, still a prefix of `bs`. -/
theorem server_write_acc (γm : GName) (cn : Nat) (γ : EchoNames) (st : NetEnd) (bs : List w8) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ echoName γm cn γ -∗ sentLb (Gg := Gg) γ.up bs -∗
      □ (∀ (w rs : List w8), ⌜w ++ rs = bs⌝ -∗ srvP cn γ st w none -∗
        |={⊤,∅}=> ∃ st0 d, netEnd G cn true st0 ∗ netDir G cn true d ∗
          ∀ k res d', ⌜WriteOutcome st0 d rs k res d'⌝ -∗ netEnd G cn true st0 -∗
            netDir G cn true d' ={∅,⊤}=∗ srvP cn γ st (w ++ rs.take k) res) := by
  iintro #Hinv #Hname #Hbs
  imodintro
  iintro %w %rs %Hwrs HP
  unfold srvP
  icases HP with ⟨Hend, Hsrv⟩
  iinv Hinv with Hi Hclose
  imod Hi
  icases echoState_lookup γm cn γ $$ Hname Hi with ⟨Hc, Hback⟩
  unfold connInv
  icases Hc with ⟨Hu, Hd, He⟩
  unfold dirInv
  icases Hd with ⟨%d, %W, %R, Hdir, Hw, Hr, %Hok⟩
  unfold echoConn
  icases He with ⟨%Wd, Hwd, Hsrv', -⟩
  unfold echoSrv
  letI := (G (Gg := Gg)).allG
  icases ghostVar_agree $$ Hsrv' Hsrv with %Heq
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hdir
  iintro %k %res %d' %Hwr Hend Hdir
  imod Hmask
  imod wire.sentAll_app γ.down W Wd (rs.take k) $$ Hw Hwd with ⟨%Heq, Hw, Hwd⟩
  subst Heq
  imod ghostVar_update_halves (W ++ rs.take k) $$ Hsrv' Hsrv with ⟨Hsrv', Hsrv⟩
  imod Hclose $$ [Hback Hu Hdir Hw Hr Hwd Hsrv'] with -
  · inext
    iapply Hback
    iframe Hu
    isplitl [Hdir Hw Hr]
    · iexists d', W ++ rs.take k, R
      iframe Hdir Hw Hr
      ipureintro; exact Net.dirOk_write Hok Hwr
    · iexists W ++ rs.take k
      iframe Hwd Hsrv'
      iexists bs
      iframe Hbs
      ipureintro
      rw [← Hwrs]
      exact (List.prefix_append_right_inj W).2 (List.take_prefix k rs)
  imodintro
  iframe Hend Hsrv

/-- The client's check: a reply it read (`resp`, a prefix of the server's bytes) is a prefix of
the client's own bytes `W`. -/
theorem client_check (γm : GName) (cn : Nat) (γ : EchoNames) (W resp : List w8) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ echoName γm cn γ -∗
      sentAll (Gg := Gg) γ.up W -∗ sentLb (Gg := Gg) γ.down resp ={⊤}=∗
      ⌜resp <+: W⌝ ∗ sentAll (Gg := Gg) γ.up W := by
  iintro #Hinv #Hname Hmy #Hresp
  iinv Hinv with Hi Hclose
  imod Hi
  icases echoState_lookup γm cn γ $$ Hname Hi with ⟨Hc, Hback⟩
  unfold connInv
  icases Hc with ⟨Hu, Hd, He⟩
  unfold echoConn
  icases He with ⟨%Wd, Hwd, Hcase⟩
  icases wire.sentLb_prefix γ.down Wd resp $$ Hwd Hresp with %Hrs
  icases Hcase with ⟨Hsrv, %si, #Hsi, %Hso⟩
  icases wire.sentLb_prefix γ.up W si $$ Hmy Hsi with %Hsio
  imod Hclose $$ [Hback Hu Hd Hwd Hsrv] with -
  · inext
    iapply Hback
    iframe Hu Hd
    iexists Wd
    iframe Hwd Hsrv
    iexists si
    iframe Hsi
    ipureintro; exact Hso
  imodintro
  iframe Hmy
  ipureintro; exact Hrs.trans (Hso.trans Hsio)

/-- The protocol's invariants on a fresh network, from `srvAddr`'s pending set (empty). -/
theorem echoInvs_alloc :
    netPend (G (Gg := Gg)) srvAddr ∅ ={⊤}=∗ ∃ γm, echoInvs (Gg := Gg) γm := by
  iintro Hpend
  letI := (G (Gg := Gg)).allG
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := EchoNames) with ⟨%γm, Hm⟩
  imod inv_alloc echoN ⊤ (echoState (Gg := Gg) γm) $$ [Hm] with #HechoInv
  · inext
    unfold echoState
    iexists ∅
    iframe Hm
    iapply BigSepM.bigSepM_empty.2
    iempintro
  imod wire.addrInv_alloc addrN srvAddr (connProto (Gg := Gg) γm) $$ Hpend with #HaddrInv
  imodintro
  iexists γm
  unfold echoInvs
  iframe HaddrInv HechoInv

end ghost

end github_com.mit_pdos.etcd_grove.examples.net.echo
end Perennial

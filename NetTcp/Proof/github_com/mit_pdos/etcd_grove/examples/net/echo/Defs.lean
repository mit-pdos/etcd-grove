/-
The protocol of `examples/net/echo`, over the TCP extension's resources (`GooseLang/Ext/Tcp`), the
per-address protocol (`wire/Addr.lean`) and the per-direction stream protocol (`wire/Stream.lean`):

* **Every connection** `cn` to `srvAddr` has ghost names `γ` (`echoName γm cn γ`, persistent: the
  ghost map `γm`): the two directions' stream protocols (`γ.up`, from the dialer; `γ.down`, from
  the acceptor) and a token (`γ.tok`). Its state (`connInv cn γ`) is both directions' `dirInv`s and
  the echo state (`echoConn γ`): the acceptor's written bytes `Wd` (the writer's half
  `sentAll γ.down Wd`) are a prefix of a lower bound `si` of what the dialer has written
  (`sentLb γ.up si`), or nothing while the server still holds the token (`echoTok`, exclusive: the
  right to make the one write). All connections' states are in one invariant (`echoState γm`), so
  that every resource the protocol moves is timeless; each direction's `inv echoN (dirInv …)`,
  which `Stream.lean`'s updates take, is derived from it (`echo_dirInv_up`/`_down`, `inv_alter`).
* **The connection's protocol** `connProto γm cn`, which every dialer deposits in `srvAddr`'s
  invariant (`echo_deposit`, through `wire.dial_both_au`) and the server takes when it accepts `cn`
  (`wire.accept_lis_au`): the acceptor end's state, the token, the reader's half of the
  up-direction (with its lower bound `sentLb γ.up []`) and the names. The dialer keeps
  `dialerOwn γm cn`: its end's state, the writer's half of the up-direction, the reader's half of
  the down-direction. A dial that fails but leaves its connection pending (abandoned, D16: the
  dialer's end closed, its direction shut and empty) deposits the same `connProto`
  (`echo_deposit_ab`): the up-direction's protocol starts from that shut direction, nothing written
  (`dirInv_body_alloc_of`), so a server that accepts it reads EOF, and the dialer keeps nothing.

The client's check (`client_check`): a reply it read (`sentLb γ.down resp`, from `Stream.read_acc`)
is a prefix of the server's bytes `Wd`, which are a prefix of the client's own (its
`sentAll γ.up`). The token makes the server's one write start from nothing (`server_write_au`).
Crashes change nothing here: the invariants are global, and a connection's protocol stays in the
address's invariant until a server (of any incarnation) accepts it.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.echo.Base
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Stream
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap ndot_mask DirNames DirOk
  dirInv sentAll sentLb rcvdAll setMap_insert setMap_lookup_none)

namespace github_com.mit_pdos.etcd_grove.examples.net.echo

/-- The server's address, as a Go string. -/
abbrev srvAddr : GoString := go!"127.0.0.1:7101"

def addrN : Namespace := nroot.@"echo_addr"
def echoN : Namespace := nroot.@"echo_conns"

/-- The ghost names of a connection: its token and its two directions' stream protocols. -/
structure EchoNames where
  tok : GName
  up : DirNames
  down : DirNames

def EchoNames.enc (γ : EchoNames) : GName × GName × GName × GName × GName :=
  (γ.tok, γ.up.w, γ.up.r, γ.down.w, γ.down.r)

instance EchoNames.countable : Pos.Countable EchoNames :=
  .ofInjective (fun γ => Pos.Countable.encode γ.enc) (fun a b h => by
    have h' := Pos.encode_inj h
    obtain ⟨t, ⟨uw, ur⟩, ⟨dw, dr⟩⟩ := a
    obtain ⟨t', ⟨uw', ur'⟩, ⟨dw', dr'⟩⟩ := b
    simp only [EchoNames.enc, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h'; rfl)

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The token of a connection: the server's right to make its one write. -/
def echoTok (γ : GName) : IProp GF := @token GF (G (Gg := Gg)).allG γ

instance echoTok_timeless (γ : GName) : Timeless (echoTok (Gg := Gg) γ) := by
  unfold echoTok; letI := (G (Gg := Gg)).allG; infer_instance

/-- The echo state of a connection with names `γ`: the acceptor's written bytes. -/
def echoConn (γ : EchoNames) : IProp GF :=
  iprop(∃ Wd : List w8, sentAll (Gg := Gg) γ.down Wd ∗
    ((echoTok γ.tok ∗ ∃ si, sentLb (Gg := Gg) γ.up si ∗ ⌜Wd <+: si⌝) ∨ ⌜Wd = []⌝))

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
  iprop(∃ γ, echoName (Gg := Gg) γm cn γ ∗ tcpEnd G cn true TcpEnd.fresh ∗ echoTok γ.tok ∗
    rcvdAll (Gg := Gg) γ.up [] ∗ sentLb (Gg := Gg) γ.up [])

instance connProto_timeless (γm : GName) (cn : Nat) : Timeless (connProto (Gg := Gg) γm cn) := by
  unfold connProto; infer_instance

/-- What the dialer keeps of its new connection `cn`. -/
def dialerOwn (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, echoName (Gg := Gg) γm cn γ ∗ tcpEnd G cn false TcpEnd.fresh ∗
    sentAll (Gg := Gg) γ.up [] ∗ rcvdAll (Gg := Gg) γ.down [] ∗ sentLb (Gg := Gg) γ.down [])

/-- The invariants of the protocol. -/
def echoInvs (γm : GName) : IProp GF :=
  iprop(inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗ inv echoN (echoState (Gg := Gg) γm))

instance echoInvs_persistent (γm : GName) : Persistent (echoInvs (Gg := Gg) γm) := by
  unfold echoInvs; infer_instance

theorem echoInvs_elim (γm : GName) :
    echoInvs (Gg := Gg) γm ⊢ inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗
      inv echoN (echoState (Gg := Gg) γm) := .rfl

theorem echoTok_exclusive (γ : GName) :
    echoTok (Gg := Gg) γ -∗ echoTok γ -∗ False := by
  unfold echoTok
  letI := (G (Gg := Gg)).allG
  iintro H1 H2
  iapply token_exclusive $$ H1 H2

/-- A direction's protocol state, from its resource, for a direction with nothing in it that is not
cut (a fresh one, or the shut one of an abandoned dial, D16): `wire.dirInv_body_alloc` for any such
direction (general: a candidate for `wire/Stream.lean`). -/
theorem dirInv_body_alloc_of (c : Nat) (s : Bool) (d : TcpDir) (hd : DirOk d [] []) :
    tcpDir (G (Gg := Gg)) c s d ==∗ ∃ γ, dirInv c s γ ∗ sentAll γ [] ∗ rcvdAll γ [] := by
  letI := (G (Gg := Gg)).allG
  iintro Hd
  imod mono_list_own_alloc (GF := GF) ([] : List w8) with ⟨%γw, Hw, -⟩
  icases (show monoListAuthOwn (GF := GF) γw 1 ([] : List w8) ⊣⊢
      iprop(monoListAuthOwn γw (1 : Qp).half [] ∗ monoListAuthOwn γw (1 : Qp).half []) by
    conv => lhs; rw [← Qp.half_add_half 1]
    exact (monoListAuthOwn_fractional γw []).fractional _ _).mp $$ Hw with ⟨Hw1, Hw2⟩
  imod ghostVar_alloc (GF := GF) ([] : List w8) with ⟨%γr, Hr⟩
  icases (ghostVar_split_half γr 1 ([] : List w8)).mp $$ Hr with ⟨Hr1, Hr2⟩
  imodintro
  iexists ⟨γw, γr⟩
  unfold dirInv sentAll rcvdAll
  isplitl [Hd Hw1 Hr1]
  · iexists d, [], []
    iframe Hd Hw1 Hr1
    ipureintro; exact hd
  iframe Hw2 Hr2

/-- The deposit of a new connection `cn`, from the acceptor's fresh end and the dialer's direction
`d` (nothing in it, not cut): both directions' stream protocols, a token, the names in the map, the
connection's state (nothing written yet); the server's part (`connProto`) and the dialer's halves
of the directions. -/
theorem echo_deposit_dir (γm : GName) (cn : Nat) (d : TcpDir) (hd : DirOk d [] []) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ tcpDir G cn false d -∗ tcpEnd G cn true TcpEnd.fresh -∗
      tcpDir G cn true TcpDir.fresh ={⊤ \ ↑addrN}=∗ connProto γm cn ∗
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
    icases tcpDir_excl _ cn true d TcpDir.fresh $$ Hdir Had with ⟨⟩
  | none =>
    imod dirInv_body_alloc_of cn false d hd $$ Hdd with ⟨%γu, HIu, Hwu, Hru⟩
    imod wire.dirInv_body_alloc cn true $$ Had with ⟨%γd, HId, Hwd, Hrd⟩
    imod token_alloc (GF := GF) with ⟨%γt, Htok⟩
    ihave #Hlbu : (sentLb (Gg := Gg) γu [] : IProp GF) $$ [Hwu]
    · iapply wire.sentLb_get
      iexact Hwu
    ihave #Hlbd : (sentLb (Gg := Gg) γd [] : IProp GF) $$ [Hwd]
    · iapply wire.sentLb_get
      iexact Hwd
    imod ghost_map_insert_persist cn (⟨γt, γu, γd⟩ : EchoNames) hm $$ Hm with ⟨Hm, #Hname⟩
    imod Hclose $$ [Hm Hconns HIu HId Hwd] with -
    · inext
      iexists m.insert cn ⟨γt, γu, γd⟩
      iframe Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m cn = none by
        rw [gmap_get?_eq]; exact hm)).2
      iframe Hconns
      unfold connInv echoConn
      iframe HIu HId
      iexists []
      iframe Hwd
      iright
      ipureintro; rfl
    imodintro
    unfold connProto echoName echoTok
    isplitl [Hae Htok Hru]
    · iexists ⟨γt, γu, γd⟩
      iframe Hname Hae Htok Hru Hlbu
    · iexists ⟨γt, γu, γd⟩
      iframe Hname Hwu Hrd Hlbd

/-- A dialer's deposit for its new connection `cn` (`dial_both_au`'s `mk`): `echo_deposit_dir`
from its fresh direction; the dialer keeps `dialerOwn`. -/
theorem echo_deposit (γm : GName) (cn : Nat) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ tcpConnAt G cn srvAddr -∗ tcpFresh G cn false -∗
      tcpFresh G cn true ={⊤ \ ↑addrN}=∗ connProto γm cn ∗ dialerOwn γm cn := by
  iintro #Hinv #- Hd Ha
  unfold tcpFresh
  icases Hd with ⟨Hde, Hdd⟩
  icases Ha with ⟨Hae, Had⟩
  imod echo_deposit_dir γm cn TcpDir.fresh wire.dirOk_fresh $$ Hinv Hdd Hae Had
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
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ tcpConnAt G cn srvAddr -∗
      tcpEnd G cn false { TcpEnd.fresh with closed := true } -∗ tcpDir G cn false ⟨[], .fin⟩ -∗
      tcpFresh G cn true ={⊤ \ ↑addrN}=∗ connProto γm cn := by
  iintro #Hinv #- - Hdd Ha
  unfold tcpFresh
  icases Ha with ⟨Hae, Had⟩
  imod echo_deposit_dir γm cn ⟨[], .fin⟩ (by simp [DirOk]) $$ Hinv Hdd Hae Had with ⟨Hp, -⟩
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

/-- The server's one write on `cn` (its end's state `st` the thread's), of bytes `bs` that are a
prefix of the dialer's (`si`), with the connection's token: the echo state's bytes were nothing,
and are a prefix of `si` after. -/
theorem server_write_au (γm : GName) (cn : Nat) (γ : EchoNames) (bs si : List w8) (st : TcpEnd)
    (hbs : bs <+: si) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ echoName γm cn γ -∗ echoTok γ.tok -∗
      sentLb (Gg := Gg) γ.up si -∗ tcpEnd G cn true st -∗
      |={⊤,∅}=> ∃ st0 d, tcpEnd G cn true st0 ∗ tcpDir G cn true d ∗
        ∀ k ok d', ⌜WriteOutcome st0 d bs k ok d'⌝ -∗ tcpEnd G cn true st0 -∗
          tcpDir G cn true d' ={∅,⊤}=∗ tcpEnd G cn true st := by
  iintro #Hinv #Hname Htok #Hsi Hend
  iinv Hinv with Hi Hclose
  imod Hi
  icases echoState_lookup γm cn γ $$ Hname Hi with ⟨Hc, Hback⟩
  unfold connInv
  icases Hc with ⟨Hu, Hd, He⟩
  unfold dirInv
  icases Hd with ⟨%d, %W, %R, Hdir, Hw, Hr, %Hok⟩
  unfold echoConn
  icases He with ⟨%Wd, Hwd, Hcase⟩
  icases Hcase with (⟨Htok', -⟩ | %HWd)
  · icases echoTok_exclusive γ.tok $$ Htok Htok' with ⟨⟩
  subst HWd
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hdir
  iintro %k %ok %d' %Hwr Hend Hdir
  imod Hmask
  imod wire.sentAll_app γ.down W [] (bs.take k) $$ Hw Hwd with ⟨%Heq, Hw, Hwd⟩
  subst Heq
  imod Hclose $$ [Hback Hu Hdir Hw Hr Hwd Htok] with -
  · inext
    iapply Hback
    iframe Hu
    isplitl [Hdir Hw Hr]
    · iexists d', [] ++ bs.take k, R
      iframe Hdir Hw Hr
      ipureintro; exact wire.dirOk_write Hok Hwr
    · iexists [] ++ bs.take k
      iframe Hwd
      ileft
      iframe Htok
      iexists si
      iframe Hsi
      ipureintro
      exact (List.take_prefix k bs).trans hbs
  imodintro
  iexact Hend

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
  icases Hcase with (⟨Htk, %si, #Hsi, %Hso⟩ | %Hso)
  · icases wire.sentLb_prefix γ.up W si $$ Hmy Hsi with %Hsio
    imod Hclose $$ [Hback Hu Hd Hwd Htk] with -
    · inext
      iapply Hback
      iframe Hu Hd
      iexists Wd
      iframe Hwd
      ileft
      iframe Htk
      iexists si
      iframe Hsi
      ipureintro; exact Hso
    imodintro
    iframe Hmy
    ipureintro; exact Hrs.trans (Hso.trans Hsio)
  · subst Hso
    imod Hclose $$ [Hback Hu Hd Hwd] with -
    · inext
      iapply Hback
      iframe Hu Hd
      iexists []
      iframe Hwd
      iright
      ipureintro; rfl
    imodintro
    iframe Hmy
    ipureintro
    rw [List.prefix_nil.1 Hrs]
    exact List.nil_prefix

/-- The protocol's invariants on a fresh network, from `srvAddr`'s pending set (empty). -/
theorem echoInvs_alloc :
    tcpPend (G (Gg := Gg)) srvAddr ∅ ={⊤}=∗ ∃ γm, echoInvs (Gg := Gg) γm := by
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

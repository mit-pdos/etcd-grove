/-
The protocol of `examples/net/acceptloop`, over the TCP extension's resources (`GooseLang/Ext/Tcp`),
the per-address protocol (`wire/Addr.lean`) and the per-direction stream protocol
(`wire/Stream.lean`). It is echo's, per connection: a server goroutine handling one connection
and a client goroutine calling on one each own that connection's halves only, so neither the
goroutines of the server's accept loop nor the client's two concurrent calls need anything more.

* **Every connection** `cn` to `srvAddr` has ghost names `γ` (`connName γm cn γ`, persistent: the
  ghost map `γm`): a token (`echoTok`, exclusive: the server's right to make its one write) and
  the stream protocols of its two directions, `γ.dir false` (up, the dialer's bytes) and
  `γ.dir true` (down, the acceptor's). All connections' state is in one invariant
  (`echoState γm`): per connection both directions' `dirInv` bodies and its echo state
  (`echoConn`): the acceptor's written bytes `Wd` (the writer's half `sentAll`, kept here so the
  client can see it) are a prefix of a lower bound `si` of the dialer's (`sentLb`), or nothing
  while the server still holds the token. Every resource the protocol moves is timeless; a
  direction's invariant `inv echoN (dirInv cn s (γ.dir s))`, which `Stream.lean`'s updates take, is
  derived from `echoState`'s (`dir_inv`, `inv_alter`).
* **The dial** (`wire.dial_both_au`: the deposit made from both ends' fresh resources): the
  dialer registers the connection (`echo_register`: names, both directions' bodies, the echo
  state) and deposits for the acceptor `connProto γm cn` (its end, the token, the up direction's
  reader half), keeping its end, the up direction's writer half and the down direction's reader
  half.

The client's check (`client_check`): a reply it read is a prefix of the server's bytes, which are
a prefix of the client's own. The token makes the server's one write start from nothing
(`server_write_au`). Crashes change nothing here: the invariants are global, and a connection's
protocol stays in the address's invariant until a server (of any incarnation) accepts it.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.Base
public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Stream
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Tcp
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv setMap ndot_mask DirNames
  dirInv sentAll sentLb rcvdAll DirOk)

namespace github_com.mit_pdos.etcd_grove.examples.net.acceptloop

/-- The server's address, as a Go string. -/
abbrev srvAddr : GoString := go!"127.0.0.1:7103"

def addrN : Namespace := nroot.@"acceptloop_addr"
def echoN : Namespace := nroot.@"acceptloop_conns"

/-- The ghost names of a connection: its token, and the stream protocols of its directions (the
up direction's writer `uw` and reader `ur`, the down direction's `dw` and `dr`). -/
structure ConnG where
  tok : GName
  uw : GName
  ur : GName
  dw : GName
  dr : GName
deriving DecidableEq

def ConnG.enc (γ : ConnG) := (γ.tok, γ.uw, γ.ur, γ.dw, γ.dr)

instance ConnG.countable : Pos.Countable ConnG :=
  .ofInjective (fun γ => Pos.Countable.encode γ.enc) (fun a b h => by
    have h' := Pos.encode_inj h
    cases a; cases b; simp only [ConnG.enc, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h'; rfl)

/-- The stream protocol's names of the direction from the end `s` (`false`: up, `true`: down). -/
def ConnG.dir (γ : ConnG) : Bool → DirNames
  | false => ⟨γ.uw, γ.ur⟩
  | true => ⟨γ.dw, γ.dr⟩

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt tcpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The token of a connection: the server's right to make its one write. -/
def echoTok (γ : GName) : IProp GF := @token GF (G (Gg := Gg)).allG γ

instance echoTok_timeless (γ : GName) : Timeless (echoTok (Gg := Gg) γ) := by
  unfold echoTok; letI := (G (Gg := Gg)).allG; infer_instance

/-- The echo state of a connection with names `γ`: the acceptor's written bytes are a prefix of
the dialer's, or nothing while the server holds the token. -/
def echoConn (γ : ConnG) : IProp GF :=
  iprop(∃ Wd : List w8, sentAll (Gg := Gg) (γ.dir true) Wd ∗
    ((echoTok γ.tok ∗ ∃ si, sentLb (γ.dir false) si ∗ ⌜Wd <+: si⌝) ∨ ⌜Wd = []⌝))

instance echoConn_timeless (γ : ConnG) : Timeless (echoConn (Gg := Gg) γ) := by
  unfold echoConn; infer_instance

/-- A connection's part of the protocol's invariant: both directions, and its echo state. -/
def connBody (cn : Nat) (γ : ConnG) : IProp GF :=
  iprop(dirInv (Gg := Gg) cn false (γ.dir false) ∗ dirInv (Gg := Gg) cn true (γ.dir true) ∗
    echoConn γ)

instance connBody_timeless (cn : Nat) (γ : ConnG) : Timeless (connBody (Gg := Gg) cn γ) := by
  unfold connBody; infer_instance

/-- Every connection's state, their names in the ghost map `γm`. -/
def echoState (γm : GName) : IProp GF :=
  iprop(∃ m : GMap Nat ConnG, @ghostMapAuth GF (G (Gg := Gg)).allG _ _ _ _ γm 1 m ∗
    [∗map] cn ↦ γ ∈ m, connBody cn γ)

/-- The connection `cn`'s names are `γ`. -/
def connName (γm : GName) (cn : Nat) (γ : ConnG) : IProp GF :=
  @ghostMapElem GF (G (Gg := Gg)).allG _ _ _ _ γm cn .discard γ

instance connName_persistent (γm : GName) (cn : Nat) (γ : ConnG) :
    Persistent (connName (Gg := Gg) γm cn γ) := by
  unfold connName; letI := (G (Gg := Gg)).allG; infer_instance

instance connName_timeless (γm : GName) (cn : Nat) (γ : ConnG) :
    Timeless (connName (Gg := Gg) γm cn γ) := by
  unfold connName; letI := (G (Gg := Gg)).allG; infer_instance

/-- What the server gets when it accepts `cn`: its end, the token, and the up direction's reader
half (with the lower bound `[]` of what was written, which its reads start from). -/
def connProto (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, tcpEnd G cn true TcpEnd.fresh ∗ echoTok γ.tok ∗ rcvdAll (γ.dir false) [] ∗
    sentLb (γ.dir false) [] ∗ connName γm cn γ)

instance connProto_timeless (γm : GName) (cn : Nat) : Timeless (connProto (Gg := Gg) γm cn) := by
  unfold connProto; infer_instance

/-- What the dialer keeps of its new connection `cn`: its end, the up direction's writer half
and the down direction's reader half (with the lower bound `[]`). -/
def dialerOwn (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, tcpEnd G cn false TcpEnd.fresh ∗ sentAll (γ.dir false) [] ∗
    rcvdAll (γ.dir true) [] ∗ sentLb (γ.dir true) [] ∗ connName γm cn γ)

/-- The invariants of the protocol. -/
def echoInvs (γm : GName) : IProp GF :=
  iprop(inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗ inv echoN (echoState (Gg := Gg) γm))

instance echoInvs_persistent (γm : GName) : Persistent (echoInvs (Gg := Gg) γm) := by
  unfold echoInvs; infer_instance

theorem echoInvs_elim (γm : GName) :
    echoInvs (Gg := Gg) γm ⊢ inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗
      inv echoN (echoState (Gg := Gg) γm) := .rfl

theorem echoTok_exclusive (γ : GName) :
    echoTok (Gg := Gg) γ -∗ echoTok (Gg := Gg) γ -∗ False := by
  unfold echoTok
  letI := (G (Gg := Gg)).allG
  iintro H1 H2
  iapply token_exclusive $$ H1 H2

/-- A direction's invariant, from the protocol's: its body is a part of `echoState`'s. -/
theorem dir_inv (γm : GName) (cn : Nat) (γ : ConnG) (s : Bool) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ connName γm cn γ -∗
      inv echoN (dirInv (Gg := Gg) cn s (γ.dir s)) := by
  iintro #Hinv #Hname
  iapply inv_alter $$ Hinv
  inext
  imodintro
  iintro HP
  unfold echoState
  icases HP with ⟨%m, Hm, Hconns⟩
  letI := (G (Gg := Gg)).allG
  unfold connName
  icases ghost_map_lookup $$ Hm Hname with %Hl
  icases (BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some γ by
    rw [gmap_get?_eq]; exact Hl)).1 $$ Hconns with ⟨Hc, Hback⟩
  unfold connBody
  icases Hc with ⟨Hu, Hd, He⟩
  cases s
  · iframe Hu
    iintro Hu
    iexists m
    iframe Hm
    iapply Hback
    iframe Hu Hd He
  · iframe Hd
    iintro Hd
    iexists m
    iframe Hm
    iapply Hback
    iframe Hu Hd He

/-- The dialer's registration of its new connection `cn` (from both ends' fresh resources): its
names, both directions and its echo state in the invariant; the acceptor's deposit, and the
dialer's halves. -/
theorem echo_register (γm : GName) (cn : Nat) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ tcpFresh G cn false -∗ tcpFresh G cn true
      ={⊤ \ ↑addrN}=∗ connProto γm cn ∗ dialerOwn γm cn := by
  iintro #Hinv Hd Ha
  iinv Hinv with Hi Hclose
  · exact ndot_mask nroot "acceptloop_conns" "acceptloop_addr" (by decide)
  unfold echoState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  unfold tcpFresh
  icases Hd with ⟨Hde, Hdd⟩
  icases Ha with ⟨Hae, Had⟩
  letI := (G (Gg := Gg)).allG
  cases hm : m.lookup cn with
  | some γ' =>
    -- `cn` is new: its up direction is owned once
    icases (BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some γ' by
      rw [gmap_get?_eq]; exact hm)).1 $$ Hconns with ⟨Hc, -⟩
    unfold connBody dirInv
    icases Hc with ⟨⟨%d, %W, %R, Hd', -⟩, -⟩
    icases tcpDir_excl _ cn false _ _ $$ Hdd Hd' with ⟨⟩
  | none =>
    imod wire.dirInv_body_alloc cn false $$ Hdd with ⟨%γu, Hu, Hsu, Hru⟩
    imod wire.dirInv_body_alloc cn true $$ Had with ⟨%γd, Hdn, Hsd, Hrd⟩
    imod token_alloc (GF := GF) with ⟨%γt, Htok⟩
    let γ : ConnG := ⟨γt, γu.w, γu.r, γd.w, γd.r⟩
    have hu : γ.dir false = γu := rfl
    have hd : γ.dir true = γd := rfl
    ihave #Hlbu := wire.sentLb_get γu [] $$ Hsu
    ihave #Hlbd := wire.sentLb_get γd [] $$ Hsd
    imod ghost_map_insert_persist cn γ hm $$ Hm with ⟨Hm, #Hname⟩
    imod Hclose $$ [Hm Hconns Hu Hdn Hsd] with -
    · inext
      iexists m.insert cn γ
      iframe Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m cn = none by
        rw [gmap_get?_eq]; exact hm)).2
      iframe Hconns
      unfold connBody echoConn
      rw [hu, hd]
      iframe Hu Hdn
      iexists []
      iframe Hsd
      iright
      ipureintro; rfl
    imodintro
    unfold connProto dialerOwn
    isplitl [Hae Htok Hru]
    · iexists γ
      unfold echoTok connName
      rw [hu]
      iframe Hae Htok Hru Hlbu Hname
    · iexists γ
      unfold connName
      rw [hu, hd]
      iframe Hde Hsu Hrd Hlbd Hname

/-- The server's one write on `cn`, of bytes `bs` that are a prefix of the dialer's (`si`), with
the connection's token: the echo state's bytes were nothing, and are a prefix of `si` after. -/
theorem server_write_au (γm : GName) (cn : Nat) (γ : ConnG) (bs si : List w8) (st : TcpEnd)
    (hbs : bs <+: si) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ connName γm cn γ -∗ echoTok γ.tok -∗
      sentLb (γ.dir false) si -∗ tcpEnd G cn true st -∗
      |={⊤,∅}=> ∃ st0 d, tcpEnd G cn true st0 ∗ tcpDir G cn true d ∗
        ∀ k ok d', ⌜WriteOutcome st0 d bs k ok d'⌝ -∗ tcpEnd G cn true st0 -∗
          tcpDir G cn true d' ={∅,⊤}=∗ tcpEnd G cn true st := by
  iintro #Hinv #Hname Htok #Hsi Hend
  iinv Hinv with Hi Hclose
  unfold echoState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  letI := (G (Gg := Gg)).allG
  unfold connName
  icases ghost_map_lookup $$ Hm Hname with %Hl
  icases (BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some γ by
    rw [gmap_get?_eq]; exact Hl)).1 $$ Hconns with ⟨Hc, Hback⟩
  unfold connBody echoConn
  icases Hc with ⟨Hu, Hdn, %Wd, Hsd, Hcase⟩
  icases Hcase with (⟨Htok', -⟩ | %HWd)
  · icases echoTok_exclusive γ.tok $$ Htok Htok' with ⟨⟩
  subst HWd
  unfold dirInv
  icases Hdn with ⟨%d, %W, %R, Hd, Hw, Hr, %Hok⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %k %ok %d' %Hwr Hend Hd
  imod Hmask
  imod wire.sentAll_app (γ.dir true) W [] (bs.take k) $$ Hw Hsd with ⟨%Heq, Hw, Hsd⟩
  subst Heq
  imod Hclose $$ [Hm Hback Hu Hd Hw Hr Hsd Htok] with -
  · inext
    iexists m
    iframe Hm
    iapply Hback
    iframe Hu
    isplitl [Hd Hw Hr]
    · iexists d', [] ++ bs.take k, R
      iframe Hd Hw Hr
      ipureintro; exact wire.dirOk_write Hok Hwr
    iexists [] ++ bs.take k
    iframe Hsd
    ileft
    iframe Htok
    iexists si
    iframe Hsi
    ipureintro
    exact (List.take_prefix k bs).trans hbs
  imodintro
  iexact Hend

/-- The client's check: a reply it read (`resp`, a lower bound of the server's bytes) is a prefix
of the client's own bytes `W`. -/
theorem client_check (γm : GName) (cn : Nat) (γ : ConnG) (W resp : List w8) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ connName γm cn γ -∗
      sentAll (γ.dir false) W -∗ sentLb (γ.dir true) resp ={⊤}=∗
      ⌜resp <+: W⌝ ∗ sentAll (γ.dir false) W := by
  iintro #Hinv #Hname Hmy #Hresp
  iinv Hinv with Hi Hclose
  unfold echoState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  letI := (G (Gg := Gg)).allG
  unfold connName
  icases ghost_map_lookup $$ Hm Hname with %Hl
  icases (BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some γ by
    rw [gmap_get?_eq]; exact Hl)).1 $$ Hconns with ⟨Hc, Hback⟩
  unfold connBody echoConn
  icases Hc with ⟨Hu, Hdn, %Wd, Hsd, Hcase⟩
  icases wire.sentLb_prefix (γ.dir true) Wd resp $$ Hsd Hresp with %Hrs
  icases Hcase with (⟨Htk, %si, #Hsi, %Hso⟩ | %Hso)
  · icases wire.sentLb_prefix (γ.dir false) W si $$ Hmy Hsi with %Hsio
    imod Hclose $$ [Hm Hback Hu Hdn Hsd Htk] with -
    · inext
      iexists m
      iframe Hm
      iapply Hback
      iframe Hu Hdn
      iexists Wd
      iframe Hsd
      ileft
      iframe Htk
      iexists si
      iframe Hsi
      ipureintro; exact Hso
    imodintro
    iframe Hmy
    ipureintro; exact Hrs.trans (Hso.trans Hsio)
  · subst Hso
    imod Hclose $$ [Hm Hback Hu Hdn Hsd] with -
    · inext
      iexists m
      iframe Hm
      iapply Hback
      iframe Hu Hdn
      iexists []
      iframe Hsd
      iright
      ipureintro; rfl
    imodintro
    iframe Hmy
    ipureintro
    rw [List.prefix_nil.1 Hrs]
    exact List.nil_prefix

end wps

end github_com.mit_pdos.etcd_grove.examples.net.acceptloop
end Perennial

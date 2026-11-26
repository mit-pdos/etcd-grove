/-
The protocol of `examples/net/acceptloop`, over the net extension's resources (`GooseLang/Ext/Net`),
the per-address protocol (`wire/Addr.lean`) and the per-direction stream protocol
(`wire/Stream.lean`). It is echo's, per connection: a server goroutine handling one connection
and a client goroutine calling on one each own that connection's halves only, so neither the
goroutines of the server's accept loop nor the client's concurrent calls need anything more.

* **Every connection** `cn` to `srvAddr` has ghost names `γ` (`connName γm cn γ`, persistent: the
  ghost map `γm`): a ghost variable `γ.srv` (`srvW`, two halves: the bytes the acceptor's `Write`
  has written so far, one half the server's) and the stream protocols of its two directions,
  `γ.dir false` (up, the dialer's bytes) and `γ.dir true` (down, the acceptor's). All connections'
  state is in one invariant (`echoState γm`): per connection both directions' `dirInv` bodies and
  its echo state (`echoConn`): the acceptor's written bytes `Wd` (the writer's half `sentAll`, kept
  here so the client can see it, and the other half of `srvW`) are a prefix of a lower bound `si`
  of the dialer's (`sentLb`). Every resource the protocol moves is timeless; a direction's
  invariant `inv echoN (dirInv cn s (γ.dir s))`, which `Stream.lean`'s updates take, is derived
  from `echoState`'s (`dir_inv`, `inv_alter`).
* **The dial** (`wire.dial_both_au`: the deposit made from both ends' fresh resources): the
  dialer registers the connection (`echo_register`: names, both directions' bodies, the echo
  state) and deposits for the acceptor `connProto γm cn` (its end, its half of `srvW`, the up
  direction's reader half), keeping its end, the up direction's writer half and the down
  direction's reader half. A dial that fails leaving its connection abandoned (D16: the dialer's
  end closed, the up direction shut and empty) registers it the same way (`echo_register_ab`,
  over `echo_register_dir`, which takes the up direction in any state agreeing with nothing
  written, `wire.dirInv_body_alloc_of`), the dialer's halves dropped: a server that accepts it
  reads EOF and never writes, and nothing it could write would break a check, since no client
  reads it.

The server's `Write` is a loop of steps (D2): each step (`server_write_au`, packaged as the
accessor `net.Conn.Write.spec` takes, `server_write_acc`) extends `Wd` by the bytes it appended,
which stay a prefix of the request it read, so of `si`; the server's half of `srvW` says `Wd` is
what its earlier steps wrote. The client's check (`client_check`): a reply it read is a prefix of
the server's bytes, which are a prefix of the client's own. Crashes change nothing here: the
invariants are global, and a connection's protocol stays in the address's invariant until a server
(of any incarnation) accepts it.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.acceptloop.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Stream

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv DirNames dirInv sentAll sentLb rcvdAll)

namespace github_com.mit_pdos.etcd_grove.examples.net.acceptloop

/-- The server's address, as a Go string. -/
abbrev srvAddr : GoString := go!"127.0.0.1:7103"

def addrN : Namespace := nroot.@"acceptloop_addr"
def echoN : Namespace := nroot.@"acceptloop_conns"

/-- The ghost names of a connection: the acceptor's written bytes `srv`, and the stream protocols
of its directions (the up direction's writer `uw` and reader `ur`, the down direction's `dw` and
`dr`). -/
structure ConnG where
  srv : GName
  uw : GName
  ur : GName
  dw : GName
  dr : GName
deriving DecidableEq

def ConnG.enc (γ : ConnG) := (γ.srv, γ.uw, γ.ur, γ.dw, γ.dr)

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
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- A half of the connection's ghost variable `γ`: the acceptor has written `W` (the server's
half, and the echo state's). -/
def srvW (γ : GName) (W : List w8) : IProp GF :=
  @ghostVar GF (G (Gg := Gg)).allG _ _ γ (1 : Qp).half W

instance srvW_timeless (γ : GName) (W : List w8) : Timeless (srvW (Gg := Gg) γ W) := by
  unfold srvW; letI := (G (Gg := Gg)).allG; infer_instance

/-- The echo state of a connection with names `γ`: the acceptor's written bytes are a prefix of
the dialer's. -/
def echoConn (γ : ConnG) : IProp GF :=
  iprop(∃ Wd : List w8, sentAll (Gg := Gg) (γ.dir true) Wd ∗ srvW γ.srv Wd ∗
    ∃ si, sentLb (γ.dir false) si ∗ ⌜Wd <+: si⌝)

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

/-- What the server gets when it accepts `cn`: its end, its half of the written bytes (nothing
yet), and the up direction's reader half (with the lower bound `[]` of what was written, which its
reads start from). -/
def connProto (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, netEnd G cn true NetEnd.fresh ∗ srvW γ.srv [] ∗ rcvdAll (γ.dir false) [] ∗
    sentLb (γ.dir false) [] ∗ connName γm cn γ)

instance connProto_timeless (γm : GName) (cn : Nat) : Timeless (connProto (Gg := Gg) γm cn) := by
  unfold connProto; infer_instance

/-- What the dialer keeps of its new connection `cn`: its end, the up direction's writer half
and the down direction's reader half (with the lower bound `[]`). -/
def dialerOwn (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ γ, netEnd G cn false NetEnd.fresh ∗ sentAll (γ.dir false) [] ∗
    rcvdAll (γ.dir true) [] ∗ sentLb (γ.dir true) [] ∗ connName γm cn γ)

/-- The invariants of the protocol. -/
def echoInvs (γm : GName) : IProp GF :=
  iprop(inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗ inv echoN (echoState (Gg := Gg) γm))

instance echoInvs_persistent (γm : GName) : Persistent (echoInvs (Gg := Gg) γm) := by
  unfold echoInvs; infer_instance

theorem echoInvs_elim (γm : GName) :
    echoInvs (Gg := Gg) γm ⊢ inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗
      inv echoN (echoState (Gg := Gg) γm) := .rfl

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

/-- The dialer's registration of its new connection `cn`, from its up direction in a state `d`
that agrees with nothing written (fresh, or shut and empty for an abandoned dial) and the
acceptor's fresh resources: its names, both directions and its echo state in the invariant; the
acceptor's deposit, and the dialer's halves. -/
theorem echo_register_dir (γm : GName) (cn : Nat) (d : NetDir) (hd : DirOk d [] []) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ netDir G cn false d -∗ netFresh G cn true
      ={⊤ \ ↑addrN}=∗ connProto γm cn ∗ ∃ γ, sentAll (γ.dir false) [] ∗
        rcvdAll (γ.dir true) [] ∗ sentLb (γ.dir true) [] ∗ connName γm cn γ := by
  iintro #Hinv Hdd Ha
  iinv Hinv with Hi Hclose
  · exact ndot_mask nroot "acceptloop_conns" "acceptloop_addr" (by decide)
  unfold echoState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  unfold netFresh
  icases Ha with ⟨Hae, Had⟩
  letI := (G (Gg := Gg)).allG
  cases hm : m.lookup cn with
  | some γ' =>
    -- `cn` is new: its up direction is owned once
    icases (BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some γ' by
      rw [gmap_get?_eq]; exact hm)).1 $$ Hconns with ⟨Hc, -⟩
    unfold connBody dirInv
    icases Hc with ⟨⟨%d', %W, %R, Hd', -⟩, -⟩
    icases netDir_excl _ cn false _ _ $$ Hdd Hd' with ⟨⟩
  | none =>
    imod wire.dirInv_body_alloc_of cn false d hd $$ Hdd with ⟨%γu, Hu, Hsu, Hru⟩
    imod wire.dirInv_body_alloc cn true $$ Had with ⟨%γd, Hdn, Hsd, Hrd⟩
    imod ghostVar_alloc (GF := GF) ([] : List w8) with ⟨%γs, Hs⟩
    icases (ghostVar_split_half γs 1 ([] : List w8)).mp $$ Hs with ⟨Hs1, Hs2⟩
    let γ : ConnG := ⟨γs, γu.w, γu.r, γd.w, γd.r⟩
    have hu : γ.dir false = γu := rfl
    have hd : γ.dir true = γd := rfl
    ihave #Hlbu := wire.sentLb_get γu [] $$ Hsu
    ihave #Hlbd := wire.sentLb_get γd [] $$ Hsd
    imod ghost_map_insert_persist cn γ hm $$ Hm with ⟨Hm, #Hname⟩
    imod Hclose $$ [Hm Hconns Hu Hdn Hsd Hs1] with -
    · inext
      iexists m.insert cn γ
      iframe Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m cn = none by
        rw [gmap_get?_eq]; exact hm)).2
      iframe Hconns
      unfold connBody echoConn srvW
      rw [hu, hd]
      iframe Hu Hdn
      iexists []
      iframe Hsd Hs1
      iexists []
      iframe Hlbu
      ipureintro; exact List.nil_prefix
    imodintro
    unfold connProto
    isplitl [Hae Hs2 Hru]
    · iexists γ
      unfold srvW connName
      rw [hu]
      iframe Hae Hs2 Hru Hlbu Hname
    · iexists γ
      unfold connName
      rw [hu, hd]
      iframe Hsu Hrd Hlbd Hname

/-- The dialer's registration of its new connection `cn` (from both ends' fresh resources):
`echo_register_dir` for the fresh up direction, the dialer keeping its end. -/
theorem echo_register (γm : GName) (cn : Nat) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ netFresh G cn false -∗ netFresh G cn true
      ={⊤ \ ↑addrN}=∗ connProto γm cn ∗ dialerOwn γm cn := by
  iintro #Hinv Hd Ha
  iunfold netFresh at Hd
  icases Hd with ⟨Hde, Hdd⟩
  imod echo_register_dir γm cn NetDir.fresh Net.dirOk_fresh $$ Hinv Hdd Ha
    with ⟨Hp, %γ, Hsu, Hrd, #Hlbd, #Hname⟩
  imodintro
  iframe Hp
  unfold dialerOwn
  iexists γ
  iframe Hde Hsu Hrd Hlbd Hname

/-- The registration of an abandoned connection `cn` (D16: the dial failed, the dialer's end is
closed and its direction shut and empty): the acceptor's deposit, as for any connection (its
server reads EOF), the dialer's halves dropped. -/
theorem echo_register_ab (γm : GName) (cn : Nat) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗
      netEnd G cn false { NetEnd.fresh with closed := true } -∗ netDir G cn false ⟨[], .fin⟩ -∗
      netFresh G cn true ={⊤ \ ↑addrN}=∗ connProto γm cn := by
  iintro #Hinv - Hdd Ha
  imod echo_register_dir γm cn _ Net.dirOk_abandoned $$ Hinv Hdd Ha with ⟨Hp, -⟩
  imodintro
  iexact Hp

/-- One step of the server's `Write` on `cn` of bytes `bs`, a prefix of the dialer's (`si`), of
the bytes `rs` it has not written yet (after `w`, which it has: its half of `srvW`): the echo
state's bytes were `w`, and are `w ++ rs.take k`, still a prefix of `si`, after. -/
theorem server_write_au (γm : GName) (cn : Nat) (γ : ConnG) (bs si w rs : List w8) (st : NetEnd)
    (hbs : bs <+: si) (hw : w ++ rs = bs) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ connName γm cn γ -∗ sentLb (γ.dir false) si -∗
      srvW γ.srv w -∗ netEnd G cn true st -∗
      |={⊤,∅}=> ∃ st0 d, netEnd G cn true st0 ∗ netDir G cn true d ∗
        ∀ k res d', ⌜WriteOutcome st0 d rs k res d'⌝ -∗ netEnd G cn true st0 -∗
          netDir G cn true d' ={∅,⊤}=∗ netEnd G cn true st ∗ srvW γ.srv (w ++ rs.take k) := by
  iintro #Hinv #Hname #Hsi Hsv Hend
  iinv Hinv with Hi Hclose
  unfold echoState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  letI := (G (Gg := Gg)).allG
  unfold connName
  icases ghost_map_lookup $$ Hm Hname with %Hl
  icases (BigSepM.bigSepM_lookup_acc (show PartialMap.get? m cn = some γ by
    rw [gmap_get?_eq]; exact Hl)).1 $$ Hconns with ⟨Hc, Hback⟩
  unfold connBody echoConn
  icases Hc with ⟨Hu, Hdn, %Wd, Hsd, Hsv', -⟩
  unfold srvW
  icases ghostVar_agree $$ Hsv' Hsv with %HWd
  subst HWd
  unfold dirInv
  icases Hdn with ⟨%d, %W, %R, Hd, Hw, Hr, %Hok⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %k %res %d' %Hwr Hend Hd
  imod Hmask
  imod wire.sentAll_app (γ.dir true) W Wd (rs.take k) $$ Hw Hsd with ⟨%Heq, Hw, Hsd⟩
  subst Heq
  imod ghostVar_update_halves (W ++ rs.take k) $$ Hsv' Hsv with ⟨Hsv', Hsv⟩
  imod Hclose $$ [Hm Hback Hu Hd Hw Hr Hsd Hsv'] with -
  · inext
    iexists m
    iframe Hm
    iapply Hback
    iframe Hu
    isplitl [Hd Hw Hr]
    · iexists d', W ++ rs.take k, R
      iframe Hd Hw Hr
      ipureintro; exact Net.dirOk_write Hok Hwr
    iexists W ++ rs.take k
    iframe Hsd Hsv'
    iexists si
    iframe Hsi
    ipureintro
    subst hw
    exact ((List.prefix_append_right_inj W).2 (List.take_prefix k rs)).trans hbs
  imodintro
  iframe Hend Hsv

/-- The server's writer predicate for its `Write` on `cn` (`net.Conn.Write.spec`'s `P`): its end,
and its half of the written bytes, `w` (the `Write`'s bytes so far, the server's first). -/
def srvP (γ : ConnG) (cn : Nat) (st : NetEnd) (w : List w8) (_res : Option NetErr) : IProp GF :=
  iprop(netEnd G cn true st ∗ srvW (Gg := Gg) γ.srv w)

/-- The accessor `net.Conn.Write.spec` takes, for the server's `Write` of `bs`, a prefix of the
dialer's bytes: each step by `server_write_au`. -/
theorem server_write_acc (γm : GName) (cn : Nat) (γ : ConnG) (bs si : List w8) (st : NetEnd)
    (hbs : bs <+: si) :
    ⊢ inv echoN (echoState (Gg := Gg) γm) -∗ connName γm cn γ -∗ sentLb (γ.dir false) si -∗
      □ (∀ (w rs : List w8), ⌜w ++ rs = bs⌝ -∗ srvP γ cn st w none -∗
        |={⊤,∅}=> ∃ st0 d, netEnd G cn true st0 ∗ netDir G cn true d ∗
          ∀ k res d', ⌜WriteOutcome st0 d rs k res d'⌝ -∗ netEnd G cn true st0 -∗
            netDir G cn true d' ={∅,⊤}=∗ srvP γ cn st (w ++ rs.take k) res) := by
  iintro #Hinv #Hname #Hsi
  imodintro
  iintro %w %rs %hw HP
  unfold srvP
  icases HP with ⟨Hend, Hsv⟩
  iapply server_write_au γm cn γ bs si w rs st hbs hw $$ Hinv Hname Hsi Hsv Hend

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
  icases Hc with ⟨Hu, Hdn, %Wd, Hsd, Hsv, %si, #Hsi, %Hso⟩
  icases wire.sentLb_prefix (γ.dir true) Wd resp $$ Hsd Hresp with %Hrs
  icases wire.sentLb_prefix (γ.dir false) W si $$ Hmy Hsi with %Hsio
  imod Hclose $$ [Hm Hback Hu Hdn Hsd Hsv] with -
  · inext
    iexists m
    iframe Hm
    iapply Hback
    iframe Hu Hdn
    iexists Wd
    iframe Hsd Hsv
    iexists si
    iframe Hsi
    ipureintro; exact Hso
  imodintro
  iframe Hmy
  ipureintro; exact Hrs.trans (Hso.trans Hsio)

end wps

end github_com.mit_pdos.etcd_grove.examples.net.acceptloop
end Perennial

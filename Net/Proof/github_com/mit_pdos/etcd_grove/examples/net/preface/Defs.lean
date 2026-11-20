/-
The protocol of `examples/net/preface`, over the net extension's resources (`GooseLang/Ext/Net`),
the shared per-address protocol (`wire/Addr.lean`) and the per-direction stream protocol
(`wire/Stream.lean`). As echo's, with the preface skipped:

* **Every connection** `cn` to `srvAddr` has ghost names `ν` (`pfName γm cn ν`, persistent: the
  ghost map `γm`): the server's progress `ν.srv` (a ghost variable, half of it the server's:
  `pfSrv ν.srv W`, the bytes it has written on the connection), and the stream protocols of its two
  directions, `ν.up` (from the dialer, false) and `ν.down` (from the acceptor, true). All
  connections' state is in one invariant (`pfState γm`), so that every resource the protocol moves
  is timeless: for each connection, both directions' `dirInv`s (the semantics' unread bytes tied to
  what was written and read) and its reply state (`pfReply ν`): the server's written bytes `W` on
  the down direction (the writer's half, `sentAll ν.down W`, kept here so the client can bound
  them, and the other half of `ν.srv`) are a prefix of what the dialer had written past its first
  `preLen` (4) bytes (`si.drop 4`, of a lower bound `si`, `sentLb ν.up si`). `pf_dirInv` derives
  each direction's own invariant (`inv pfN (dirInv ..)`, `inv_alter`) for `Stream.lean`'s updates.
* **The connection's protocol** `connProto γm cn`, which every dialer deposits in `srvAddr`'s
  invariant (`pf_dial_au`: the dial's update, which gets both ends' fresh resources) and the server
  takes when it accepts `cn` (`wire.accept_lis_au`): the acceptor end's state, the server's half of
  `ν.srv` (nothing written), the reader's half of the up direction, and the names. The dialer keeps
  its end's state, the writer's half of the up direction and the reader's half of the down direction
  (`clientRes`). A dial that fails leaving its connection abandoned (D16: the dialer's end closed,
  its direction shut and empty) deposits the same protocol (`pf_deposit_ab`), its up direction's
  protocol started from that shut, empty direction (`wire.dirInv_body_alloc_of`), and the dialer
  keeps nothing: the server that accepts it reads EOF.

The client's check (`client_check`): a reply it read is a prefix of the server's bytes (`sentLb`
from its read), which are a prefix of the client's own past its preface (its `sentAll ν.up`). The
server's `Write` is Go's loop of steps (D2): its writer predicate `srvP` holds its half of `ν.srv`,
so each step (`server_write_acc`, the accessor of `net.Conn.Write.spec`) extends the reply state's
bytes by what it appended, still a prefix of `si.drop 4` when the whole `Write`'s bytes are.
Crashes change nothing here: the invariants are global, and a connection's protocol stays in the
address's invariant until a server (of any incarnation) accepts it.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.preface.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Stream

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.etcd_grove.examples.net.wire (G addrInv DirNames dirInv sentAll sentLb rcvdAll)

namespace github_com.mit_pdos.etcd_grove.examples.net.preface

/-- The server's address, as a Go string. -/
abbrev srvAddr : GoString := go!"127.0.0.1:7107"

def addrN : Namespace := nroot.@"preface_addr"
def pfN : Namespace := nroot.@"preface_conns"

/-- The number of bytes of the preface, which the server's reply skips. -/
abbrev preLen : Nat := 4

/-- A prefix of `b` past its first `n` bytes is past the first `n` bytes of a prefix of `b`. -/
theorem drop_prefix {α : Type} {a b : List α} (h : a <+: b) (n : Nat) : a.drop n <+: b.drop n := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t.drop (n - a.length), List.drop_append.symm⟩

/-- The ghost names of a connection: the server's progress, and the stream protocols of the
direction from the dialer (`up`) and from the acceptor (`down`). -/
structure PfNames where
  srv : GName
  up : DirNames
  down : DirNames

def PfNames.enc (ν : PfNames) := (ν.srv, ν.up.w, ν.up.r, ν.down.w, ν.down.r)

instance PfNames.countable : Pos.Countable PfNames :=
  .ofInjective (fun ν => Pos.Countable.encode ν.enc) (fun a b h => by
    have h' := Pos.encode_inj h
    obtain ⟨t, ⟨uw, ur⟩, ⟨dw, dr⟩⟩ := a
    obtain ⟨t', ⟨uw', ur'⟩, ⟨dw', dr'⟩⟩ := b
    simp only [PfNames.enc, Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h'; rfl)

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The server's progress on a connection: it has written `W` on it (a half of a ghost variable;
the reply state holds the other half). -/
def pfSrv (γ : GName) (W : List w8) : IProp GF :=
  @ghostVar GF (G (Gg := Gg)).allG _ _ γ (1 : Qp).half W

instance pfSrv_timeless (γ : GName) (W : List w8) : Timeless (pfSrv (Gg := Gg) γ W) := by
  unfold pfSrv; letI := (G (Gg := Gg)).allG; infer_instance

/-- The reply state of the connection with names `ν`: the server's written bytes `W` (the
writer's half of the down direction, and the other half of the server's progress), a prefix of
the dialer's bytes past the preface. -/
def pfReply (ν : PfNames) : IProp GF :=
  iprop(∃ W si, sentAll (Gg := Gg) ν.down W ∗ pfSrv ν.srv W ∗ sentLb ν.up si ∗
    ⌜W <+: si.drop preLen⌝)

instance pfReply_timeless (ν : PfNames) : Timeless (pfReply (Gg := Gg) ν) := by
  unfold pfReply; infer_instance

/-- The state of the connection `cn` with names `ν`: its directions' protocols and its reply
state. -/
def pfConn (cn : Nat) (ν : PfNames) : IProp GF :=
  iprop(dirInv (Gg := Gg) cn false ν.up ∗ dirInv (Gg := Gg) cn true ν.down ∗ pfReply ν)

instance pfConn_timeless (cn : Nat) (ν : PfNames) : Timeless (pfConn (Gg := Gg) cn ν) := by
  unfold pfConn; infer_instance

/-- Every connection's state, their names in the ghost map `γm`. -/
def pfState (γm : GName) : IProp GF :=
  iprop(∃ m : GMap Nat PfNames, @ghostMapAuth GF (G (Gg := Gg)).allG _ _ _ _ γm 1 m ∗
    [∗map] cn ↦ ν ∈ m, pfConn cn ν)

instance pfState_timeless (γm : GName) : Timeless (pfState (Gg := Gg) γm) := by
  unfold pfState; letI := (G (Gg := Gg)).allG; infer_instance

/-- The connection `cn`'s names are `ν`. -/
def pfName (γm : GName) (cn : Nat) (ν : PfNames) : IProp GF :=
  @ghostMapElem GF (G (Gg := Gg)).allG _ _ _ _ γm cn .discard ν

instance pfName_persistent (γm : GName) (cn : Nat) (ν : PfNames) :
    Persistent (pfName (Gg := Gg) γm cn ν) := by
  unfold pfName; letI := (G (Gg := Gg)).allG; infer_instance

instance pfName_timeless (γm : GName) (cn : Nat) (ν : PfNames) :
    Timeless (pfName (Gg := Gg) γm cn ν) := by
  unfold pfName; letI := (G (Gg := Gg)).allG; infer_instance

/-- What the server gets when it accepts `cn`: its end's state, its progress (nothing written),
the reader's half of the up direction (nothing read) and its lower bound, and the names. -/
def connProto (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ ν, netEnd G cn true NetEnd.fresh ∗ pfSrv (Gg := Gg) ν.srv [] ∗ rcvdAll ν.up [] ∗
    sentLb ν.up [] ∗ pfName γm cn ν)

instance connProto_timeless (γm : GName) (cn : Nat) : Timeless (connProto (Gg := Gg) γm cn) := by
  unfold connProto; infer_instance

/-- What the dialer keeps of its new connection `cn`: its end's state, the writer's half of the up
direction, the reader's half of the down direction (and its lower bound), and the names. -/
def clientRes (γm : GName) (cn : Nat) : IProp GF :=
  iprop(∃ ν, netEnd G cn false NetEnd.fresh ∗ sentAll (Gg := Gg) ν.up [] ∗ rcvdAll ν.down [] ∗
    sentLb ν.down [] ∗ pfName γm cn ν)

/-- The invariants of the protocol. -/
def pfInvs (γm : GName) : IProp GF :=
  iprop(inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗ inv pfN (pfState (Gg := Gg) γm))

instance pfInvs_persistent (γm : GName) : Persistent (pfInvs (Gg := Gg) γm) := by
  unfold pfInvs; infer_instance

theorem pfInvs_elim (γm : GName) :
    pfInvs (Gg := Gg) γm ⊢ inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) ∗
      inv pfN (pfState (Gg := Gg) γm) := .rfl

/-- A connection's state, from the map's: it and the wand that puts it back. -/
theorem pfConns_acc (m : GMap Nat PfNames) (cn : Nat) (ν : PfNames) (Hl : m.lookup cn = some ν) :
    ([∗map] k ↦ v ∈ m, pfConn (Gg := Gg) k v) ⊢
      pfConn cn ν ∗ (pfConn cn ν -∗ [∗map] k ↦ v ∈ m, pfConn (Gg := Gg) k v) := by
  iintro Hconns
  icases BigSepM.bigSepM_insert_acc (show PartialMap.get? m cn = some ν by
    rw [gmap_get?_eq]; exact Hl) $$ Hconns with ⟨Hc, Hback⟩
  iframe Hc
  iintro Hc
  have hm : PartialMap.insert m cn ν = m := by
    show m.insert cn ν = m
    apply GMap.ext; intro k; simp only [GMap.lookup_insert_eq_iff]
    split <;> simp_all
  have hconv : ([∗map] k ↦ v ∈ PartialMap.insert m cn ν, pfConn (Gg := Gg) k v) ⊢
      [∗map] k ↦ v ∈ m, pfConn (Gg := Gg) k v := by rw [hm]
  iapply hconv
  iapply Hback $$ Hc

/-- A connection's state, from the invariant's: it and the wand that puts it back. -/
theorem pfState_acc (γm : GName) (cn : Nat) (ν : PfNames) :
    pfName (Gg := Gg) γm cn ν ⊢ pfState γm -∗ pfConn cn ν ∗ (pfConn cn ν -∗ pfState γm) := by
  letI := (G (Gg := Gg)).allG
  iintro #Hname Hi
  unfold pfState
  icases Hi with ⟨%m, Hm, Hconns⟩
  unfold pfName
  icases ghost_map_lookup $$ Hm Hname with %Hl
  icases pfConns_acc m cn ν Hl $$ Hconns with ⟨Hc, Hback⟩
  iframe Hc
  iintro Hc
  iexists m
  iframe Hm
  iapply Hback $$ Hc

/-- Each direction's own invariant, from the protocol's (`inv_alter`), for `Stream.lean`'s
updates. -/
theorem pf_dirInv (γm : GName) (cn : Nat) (ν : PfNames) :
    ⊢ inv pfN (pfState (Gg := Gg) γm) -∗ pfName γm cn ν -∗
      inv pfN (dirInv cn false ν.up) ∗ inv pfN (dirInv cn true ν.down) := by
  iintro #Hinv #Hname
  isplitl []
  · iapply inv_alter pfN _ _ $$ Hinv
    inext; imodintro
    iintro Hi
    icases pfState_acc γm cn ν $$ Hname Hi with ⟨Hc, Hback⟩
    unfold pfConn
    icases Hc with ⟨Hup, Hdown, Hrep⟩
    iframe Hup
    iintro Hup
    iapply Hback
    iframe Hup Hdown Hrep
  · iapply inv_alter pfN _ _ $$ Hinv
    inext; imodintro
    iintro Hi
    icases pfState_acc γm cn ν $$ Hname Hi with ⟨Hc, Hback⟩
    unfold pfConn
    icases Hc with ⟨Hup, Hdown, Hrep⟩
    iframe Hdown
    iintro Hdown
    iapply Hback
    iframe Hup Hdown Hrep

/-- The new connection `cn`'s protocol, from its dialer's direction in a state `d` that agrees with
nothing written (fresh, or an abandoned dial's shut and empty direction) and the acceptor's fresh
resources: new names, both directions' protocols and the reply state (nothing written yet) in the
invariant; the server's part (`connProto`) and the dialer's halves (the writer's of the up
direction, the reader's of the down direction). -/
theorem pf_alloc (γm : GName) (cn : Nat) (d : NetDir) (hd : DirOk d [] []) :
    ⊢ inv pfN (pfState (Gg := Gg) γm) -∗ netDir G cn false d -∗ netFresh G cn true
      ={⊤ \ ↑addrN}=∗ connProto γm cn ∗ ∃ ν, sentAll (Gg := Gg) ν.up [] ∗ rcvdAll ν.down [] ∗
        sentLb ν.down [] ∗ pfName γm cn ν := by
  iintro #Hinv Hdd Ha
  iinv Hinv with Hi Hclose
  · exact ndot_mask nroot "preface_conns" "preface_addr" (by decide)
  unfold pfState
  icases Hi with ⟨%m, >Hm, >Hconns⟩
  unfold netFresh
  icases Ha with ⟨Hae, Had⟩
  letI := (G (Gg := Gg)).allG
  cases hm : m.lookup cn with
  | some ν' =>
    -- `cn` is new: the direction from its dialer is owned once
    icases pfConns_acc m cn ν' hm $$ Hconns with ⟨Hc, -⟩
    unfold pfConn dirInv
    icases Hc with ⟨⟨%d', %W, %R, Hd', -⟩, -⟩
    icases netDir_excl _ cn false d' d $$ Hd' Hdd with ⟨⟩
  | none =>
    imod ghostVar_alloc (GF := GF) ([] : List w8) with ⟨%γt, Hs⟩
    icases (ghostVar_split_half γt 1 ([] : List w8)).mp $$ Hs with ⟨Hs1, Hs2⟩
    imod wire.dirInv_body_alloc_of cn false d hd $$ Hdd with ⟨%γu, Hup, Hwu, Hru⟩
    imod wire.dirInv_body_alloc cn true $$ Had with ⟨%γd, Hdown, Hwd, Hrd⟩
    ihave #Hlbu := wire.sentLb_get γu [] $$ Hwu
    ihave #Hlbd := wire.sentLb_get γd [] $$ Hwd
    imod ghost_map_insert_persist cn (⟨γt, γu, γd⟩ : PfNames) hm $$ Hm with ⟨Hm, #Hname⟩
    imod Hclose $$ [Hm Hconns Hup Hdown Hwd Hs1] with -
    · inext
      iexists m.insert cn ⟨γt, γu, γd⟩
      iframe Hm
      iapply (BigSepM.bigSepM_insert (show PartialMap.get? m cn = none by
        rw [gmap_get?_eq]; exact hm)).2
      iframe Hconns
      unfold pfConn pfReply pfSrv
      iframe Hup Hdown
      iexists [], []
      iframe Hwd Hs1 Hlbu
      ipureintro; exact List.nil_prefix
    imodintro
    unfold connProto pfName pfSrv
    isplitl [Hae Hs2 Hru]
    · iexists ⟨γt, γu, γd⟩
      iframe Hae Hs2 Hru Hlbu Hname
    · iexists ⟨γt, γu, γd⟩
      iframe Hwu Hrd Hlbd Hname

/-- A dialer's deposit for its new connection `cn`, from both ends' fresh resources (`pf_alloc`):
the server's part (`connProto`) and the dialer's (`clientRes`). -/
theorem pf_deposit (γm : GName) (cn : Nat) :
    ⊢ inv pfN (pfState (Gg := Gg) γm) -∗ netFresh G cn false -∗ netFresh G cn true
      ={⊤ \ ↑addrN}=∗ connProto γm cn ∗ clientRes γm cn := by
  iintro #Hinv Hd Ha
  icases (show netFresh G cn false ⊢ iprop(netEnd G cn false NetEnd.fresh ∗
    netDir G cn false NetDir.fresh) from .rfl) $$ Hd with ⟨Hde, Hdd⟩
  imod pf_alloc γm cn NetDir.fresh Net.dirOk_fresh $$ Hinv Hdd Ha with
    ⟨Hp, %ν, Hwu, Hrd, #Hlbd, #Hname⟩
  imodintro
  iframe Hp
  unfold clientRes
  iexists ν
  iframe Hde Hwu Hrd Hlbd Hname

/-- An abandoned dial's deposit for its connection `cn` (D16), from the dialer's closed end, its
shut and empty direction and the acceptor's fresh resources (`pf_alloc`): the server's part
(`connProto`), the dialer's halves dropped; whoever accepts `cn` reads nothing from it but EOF. -/
theorem pf_deposit_ab (γm : GName) (cn : Nat) :
    ⊢ inv pfN (pfState (Gg := Gg) γm) -∗ netEnd G cn false { NetEnd.fresh with closed := true } -∗
      netDir G cn false ⟨[], .fin⟩ -∗ netFresh G cn true ={⊤ \ ↑addrN}=∗ connProto γm cn := by
  iintro #Hinv - Hdd Ha
  imod pf_alloc γm cn ⟨[], .fin⟩ Net.dirOk_abandoned $$ Hinv Hdd Ha with ⟨Hp, -⟩
  imodintro
  iexact Hp

/-- A dial of `srvAddr`: the update of `net.Dial` with `Qfail := True` (`wire.dial_both_au`), which
deposits the connection's protocol in the address's invariant, made from both ends' fresh resources
(`pf_deposit`), or, for an abandoned dial, from the acceptor's (`pf_deposit_ab`). -/
theorem pf_dial_au (γm : GName) :
    ⊢ inv addrN (addrInv srvAddr (connProto (Gg := Gg) γm)) -∗ inv pfN (pfState (Gg := Gg) γm) -∗
      |={⊤,∅}=> ∃ S, netPend G srvAddr S ∗
        ∀ cn, ⌜cn ∉ S⌝ -∗ netPend G srvAddr (S ∪ {[cn]}) -∗ netConnAt G cn srvAddr -∗
          netFresh G cn true -∗
          ((netFresh G cn false ={∅,⊤}=∗ clientRes γm cn) ∧
           (netEnd G cn false { NetEnd.fresh with closed := true } -∗
            netDir G cn false ⟨[], .fin⟩ ={∅,⊤}=∗ True)) := by
  iintro #HaddrInv #HpfInv
  iapply wire.dial_both_au addrN srvAddr (connProto γm) (clientRes γm) $$ HaddrInv
  · iintro %cn - Hd Ha
    iapply pf_deposit γm cn $$ HpfInv Hd Ha
  · iintro %cn - He Hd Ha
    iapply pf_deposit_ab γm cn $$ HpfInv He Hd Ha

/-- The server's writer predicate on `cn` (`net.Conn.Write.spec`'s `P`): its end's state `st`,
and its progress `w` on the connection (the bytes of its `Write` so far: it writes nothing else). -/
def srvP (cn : Nat) (ν : PfNames) (st : NetEnd) (w : List w8) (_res : Option NetErr) : IProp GF :=
  iprop(netEnd G cn true st ∗ pfSrv (Gg := Gg) ν.srv w)

/-- The accessor `net.Conn.Write.spec` takes for the server's one `Write` on `cn`, for `srvP`, of
bytes `bs` that are a prefix of the dialer's (`si`) past the preface: each step appends to the reply
state's bytes, the server's progress `w`, what it wrote, so they stay a prefix of `bs`, so of
`si.drop preLen`. -/
theorem server_write_acc (γm : GName) (cn : Nat) (ν : PfNames) (bs si : List w8) (st : NetEnd)
    (hbs : bs <+: si.drop preLen) :
    ⊢ inv pfN (pfState (Gg := Gg) γm) -∗ pfName γm cn ν -∗ sentLb ν.up si -∗
      □ (∀ (w rs : List w8), ⌜w ++ rs = bs⌝ -∗ srvP cn ν st w none -∗
        |={⊤,∅}=> ∃ st0 d, netEnd G cn true st0 ∗ netDir G cn true d ∗
          ∀ k res d', ⌜WriteOutcome st0 d rs k res d'⌝ -∗ netEnd G cn true st0 -∗
            netDir G cn true d' ={∅,⊤}=∗ srvP cn ν st (w ++ rs.take k) res) := by
  iintro #Hinv #Hname #Hsi
  imodintro
  iintro %w %rs %Hwrs HP
  unfold srvP
  icases HP with ⟨Hend, Hs⟩
  iinv Hinv with Hi Hclose
  icases Hi with >Hi
  icases pfState_acc γm cn ν $$ Hname Hi with ⟨Hc, Hback⟩
  unfold pfConn
  icases Hc with ⟨Hup, Hdown, Hrep⟩
  unfold pfReply
  icases Hrep with ⟨%W, %si0, Hw, Hs', -, -⟩
  unfold pfSrv
  letI := (G (Gg := Gg)).allG
  icases ghostVar_agree $$ Hs' Hs with %HW
  subst HW
  unfold dirInv
  icases Hdown with ⟨%d, %W', %R, Hd, Hw', Hr, %Hok⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st, d
  iframe Hend Hd
  iintro %k %res %d' %Hwr Hend Hd
  imod Hmask
  imod wire.sentAll_app ν.down W' W (rs.take k) $$ Hw' Hw with ⟨%Heq, Hw', Hw⟩
  subst Heq
  imod ghostVar_update_halves (W' ++ rs.take k) $$ Hs' Hs with ⟨Hs', Hs⟩
  imod Hclose $$ [Hback Hup Hd Hw' Hr Hw Hs'] with -
  · inext
    iapply Hback
    iframe Hup
    isplitl [Hd Hw' Hr]
    · iexists d', W' ++ rs.take k, R
      iframe Hd Hw' Hr
      ipureintro; exact Net.dirOk_write Hok Hwr
    · iexists W' ++ rs.take k, si
      iframe Hw Hs' Hsi
      ipureintro
      rw [← Hwrs] at hbs
      exact ((List.prefix_append_right_inj W').2 (List.take_prefix k rs)).trans hbs
  imodintro
  iframe Hend Hs

/-- The client's check: a reply it read (`resp`, a lower bound of the server's bytes) is a prefix
of the client's own bytes `W` past the preface. -/
theorem client_check (γm : GName) (cn : Nat) (ν : PfNames) (W resp : List w8) :
    ⊢ inv pfN (pfState (Gg := Gg) γm) -∗ pfName γm cn ν -∗ sentAll ν.up W -∗ sentLb ν.down resp
      ={⊤}=∗ ⌜resp <+: W.drop preLen⌝ ∗ sentAll ν.up W := by
  iintro #Hinv #Hname Hmy #Hresp
  iinv Hinv with Hi Hclose
  icases Hi with >Hi
  icases pfState_acc γm cn ν $$ Hname Hi with ⟨Hc, Hback⟩
  unfold pfConn
  icases Hc with ⟨Hup, Hdown, Hrep⟩
  unfold pfReply
  icases Hrep with ⟨%Wd, %si, Hwd, Hs, #Hsi, %Hso⟩
  icases wire.sentLb_prefix ν.down Wd resp $$ Hwd Hresp with %Hrs
  icases wire.sentLb_prefix ν.up W si $$ Hmy Hsi with %Hsio
  imod Hclose $$ [Hback Hup Hdown Hwd Hs] with -
  · inext
    iapply Hback
    iframe Hup Hdown
    iexists Wd, si
    iframe Hwd Hs Hsi
    ipureintro; exact Hso
  imodintro
  iframe Hmy
  ipureintro; exact Hrs.trans (Hso.trans (drop_prefix Hsio preLen))

/-- A deadline set (or cleared) by an end its thread owns: the update of `net.Conn.SetDeadline`,
which hands back the end's state, whatever its outcome. -/
theorem owned_setDeadline_au (c : Nat) (s : Bool) (st : NetEnd) (kind : w64) (set : Bool) :
    ⊢ netEnd (G (Gg := Gg)) c s st -∗
      |={⊤,∅}=> ∃ st0, netEnd G c s st0 ∗
        ∀ res st', ⌜DeadlineOutcome st0 kind set res st'⌝ -∗
          netEnd G c s st' ={∅,⊤}=∗ ∃ st'', netEnd G c s st'' := by
  iintro Hend
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists st
  iframe Hend
  iintro %res %st' - Hend
  imod Hmask
  imodintro
  iexists st'
  iexact Hend

end wps

end github_com.mit_pdos.etcd_grove.examples.net.preface
end Perennial
